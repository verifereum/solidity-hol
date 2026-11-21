(* The external entry of a contract: one call frame of the contract's code,
 * from its calldata to its return or revert data, following the dispatcher
 * of the pinned profile (solc-0.8.37-via-ir-osaka):
 *  - calldata of at least 4 bytes whose selector names an external function
 *    calls it: a nonpayable function given value reverts, then the arguments
 *    are ABI-decoded, reverting on data the decoder rejects;
 *  - otherwise empty calldata calls receive, if any, and any other calldata
 *    the fallback, which reverts on value unless payable; a fallback taking
 *    bytes is given the whole calldata, and the bytes it returns are the
 *    return data;
 *  - with neither, the call reverts.
 * Compiler-generated reverts carry no data. A return is the ABI encoding of
 * the return values, and a panic the revert data Panic(uint256).
 *
 * The frame starts from the world at frame entry: value transfer, nonces,
 * gas and the transaction around the call are Verifereum's. A revert or panic
 * restores that world, including its logs.
 *
 * The frame is the transaction's: the entry world's original accounts are the
 * world at the transaction's start, and a creation marks its own account
 * empty in them, as Verifereum's CREATE does. A frame that succeeds settles
 * the transaction, deleting the accounts its calls left pending deletion
 * (EIP-6780).
 *)
Theory solidityEntry
Ancestors
  solidityEvaluator
Libs
  cv_transLib

(* A creation that succeeds yields the values of the contract's immutables:
 * the deployed code is the compiler's, with those values in it. *)
Datatype:
  contract_result
  = ContractReturned (byte list) source_world
  | ContractCreated (num |-> scalar) source_world
  | ContractReverted (byte list) source_world
  | ContractAborted source_world
  | ContractInvalid string
  | ContractOutOfFuel
End

(* A frame's entry: an external function or receive, whose returns are ABI
 * encoded; the fallback, whose return bytes, if any, are the return data;
 * or the creation. *)
Datatype:
  entry_kind = CallEntry | FallbackEntry | CreationEntry
End

Datatype:
  dispatch_result
  = DispatchCall core_procedure (runtime_value list) entry_kind
  | DispatchRevert
  | DispatchPanic num
  | DispatchInvalid string
End

Definition lookup_external_def:
  (lookup_external sel [] = NONE) ∧
  (lookup_external sel (e :: es) =
    if e.selector = sel then SOME e else lookup_external sel es)
End

Definition dispatch_procedure_def:
  dispatch_procedure env f args kind =
    case lookup_procedure env f of
      SOME p => DispatchCall p args kind
    | NONE => DispatchInvalid "unknown procedure"
End

(* The fallback's arguments: none, or the calldata as bytes. *)
Definition fallback_arguments_def:
  fallback_arguments env f (fr : source_frame) =
    case lookup_procedure env f of
      SOME p =>
        if p.parameters = [] then []
        else [ReferenceValue (CalldataReference 0 (LENGTH fr.call_data) BytesT)]
    | NONE => []
End

Definition dispatch_def:
  dispatch env (prog : core_program) (fr : source_frame) =
    let data = fr.call_data in
    case (if 4 ≤ LENGTH data
          then lookup_external (TAKE 4 data) prog.external_functions
          else NONE) of
      SOME e =>
        if ¬e.payable ∧ fr.call_value ≠ 0 then DispatchRevert else
        (case lookup_procedure env e.external_procedure of
           NONE => DispatchInvalid "unknown procedure"
         | SOME p =>
             case decode_arguments env (MAP SND p.parameters) (DROP 4 data) 4 128 of
               INL args => DispatchCall p args CallEntry
             | INR (PanicCompletion n) => DispatchPanic n
             | INR (InvalidCompletion reason) => DispatchInvalid reason
             | INR _ => DispatchRevert)
    | NONE =>
        case (data, prog.receive_procedure, prog.fallback_procedure) of
          ([], SOME f, _) => dispatch_procedure env f [] CallEntry
        | (_, _, SOME (f, payable)) =>
            if ¬payable ∧ fr.call_value ≠ 0 then DispatchRevert
            else dispatch_procedure env f (fallback_arguments env f fr) FallbackEntry
        | _ => DispatchRevert
End

(* The return data of a fallback's values, nothing or its bytes, and the
 * state after reading them: the compiled fallback returns
 * [retval + 32, retval + 32 + mload(retval)), which raises the memory size
 * as that read does. *)
Definition fallback_output_def:
  fallback_output st vs =
    case vs of
      [] => (INL [], st)
    | [ReferenceValue r] =>
        (case byte_contents st r of
           INL (bs, st1) => (INL bs, st1)
         | INR c => (INR c, completion_memory c st))
    | _ => (INR (InvalidCompletion "bad fallback return"), st)
End

(* A frame's output, and the state after the compiled code writes the
 * encoding of its return values, and the encoder's spill past it, at the free
 * memory pointer; when the encoding panics, the panic's scratch write. *)
Definition entry_output_def:
  entry_output env p kind st vs =
    if kind = FallbackEntry then fallback_output st vs
    else case encoded_runtime_values env st (MAP SND p.return_bindings) vs of
      INL ((data, spill), st1) =>
        (INL data, let q = FST (memory_load 64 st1) in
                   memory_write (q + LENGTH data) spill (memory_write q data st1))
    | INR c => (INR c, completion_memory c st)
End

(* The end of the transaction: its pending deletions happen. *)
Definition settle_source_world_def:
  settle_source_world (w : source_world) =
    w with <| accounts := process_deletions w.to_delete w.accounts;
              to_delete := [] |>
End

(* The memory a frame starts with, as the compiler's prologue leaves it: the
 * free memory pointer at 0x40, past the reserved memory (a creation frame's
 * immutables); then, for a constructor with parameters, its arguments copied
 * to memory allocated for them. *)
Definition entry_memory_def:
  entry_memory reserved copy (st : source_state) =
    let st1 = memory_store 64 (128 + reserved) st in
    case copy of
      NONE => INL st1
    | SOME bs =>
        case allocate_memory (LENGTH bs) st1 of
          INL (p, st2) => INL (memory_write p bs st2)
        | INR c => INR c
End

(* The values of the immutables in a creation frame's reserved memory, a word
 * each from a: NONE when a word is not one its type holds, which the source
 * cannot represent. *)
Definition memory_immutables_def:
  (memory_immutables env a [] st = SOME FEMPTY) ∧
  (memory_immutables env a ((x, ty) :: rest) st =
    let w = FST (memory_load a st) in
    case word_value env ty w of
      INL (ScalarValue s) =>
        if memory_word env ty (ScalarValue s) = SOME w then
          OPTION_MAP (λimm. imm |+ (ast_key x, s))
            (memory_immutables env (a + 32) rest st)
        else NONE
    | _ => NONE)
End

(* The bytes of a state's memory, up to its size. *)
Definition memory_image_def:
  memory_image (st : source_state) = yul_mem_read st.memory 0 st.memory_size
End

(* One frame running procedure p on its arguments, with the values imm of
 * the immutables (NONE in a creation frame, which keeps them in its reserved
 * memory), and the frame's memory when it ends, which source code cannot
 * observe. An inline assembly halt returns its bytes as the frame's data; in
 * a creation frame those bytes would be the deployed code, which the source
 * does not model, so a halt there fails closed. A creation frame yields the
 * immutables' final values, the words of its reserved memory.
 *)
Definition run_entry_frame_def:
  run_entry_frame fuel env p args (fr : source_frame) (w : source_world) imm reserved
            copy kind gas =
    let w0 = if kind = CreationEntry then
               w with original :=
                 update_account fr.self_address empty_account_state w.original
             else w in
    let st = <| world := w0; frame := fr; immutables := imm; scopes := [];
                memory := FEMPTY; memory_size := 0;
                targets := FEMPTY; return_data := SOME [] |> in
    let r = case entry_memory reserved copy st of
      INR c => abrupt_result c st gas
    | INL st0 =>
      case materialize_arguments env (MAP SND p.parameters) args st0 of
        INL (values, st1) => invoke_source fuel env p.procedure_id values st1 gas
      | INR c => abrupt_result c st0 gas in
    let fin = finish_source_frame w r.state.world r.completion in
    let out = case fin of
        FrameSuccess vs _ => entry_output env p kind r.state vs
      | _ => (INL [], r.state) in
    (if r.unused_gas_evidence ≠ [] then
      ContractInvalid "unconsumed gas observation"
    else (case fin of
      FrameSuccess vs w' =>
        (case FST out of
           INL data =>
             if kind = CreationEntry then
               (case memory_immutables env 128 env.immutables r.state of
                  SOME values => ContractCreated values (settle_source_world w')
                | NONE => ContractInvalid "unsupported: an immutable's word is not one its type holds")
             else ContractReturned data (settle_source_world w')
         | INR (PanicCompletion code) => ContractReverted (panic_data code) w
         | INR (RevertCompletion data) => ContractReverted data w
         | INR (InvalidCompletion reason) => ContractInvalid reason
         | INR _ => ContractInvalid "unencodable return values")
    | FrameRevert data w' => ContractReverted data w'
    | FrameAbort w' => ContractAborted w'
    | FrameHalt data w' =>
        if kind = CreationEntry then ContractInvalid "assembly halt in a creation frame"
        else ContractReturned data (settle_source_world w')
    | FramePanic code w' => ContractReverted (panic_data code) w'
    | FrameInvalid reason => ContractInvalid reason
    | FrameResourceLimit => ContractOutOfFuel),
     memory_image (SND out))
End

Definition run_entry_with_gas_def:
  run_entry_with_gas fuel env p args fr w imm reserved copy kind gas =
    FST (run_entry_frame fuel env p args fr w imm reserved copy kind gas)
End

Definition run_entry_def:
  run_entry fuel env p args fr w imm reserved copy kind =
    run_entry_with_gas fuel env p args fr w imm reserved copy kind []
End

(* Dispatch can end a frame before its body reads any evidence. *)
Definition unconsumed_gas_result_def:
  unconsumed_gas_result gas r =
    if gas = ([] : gas_observation list) then r
    else ContractInvalid "unconsumed gas observation"
End

(* A call of the deployed contract, whose immutables have the values imm, with
 * its frame's final memory; NONE when dispatch ends it before a frame runs. *)
Definition call_contract_frame_def:
  call_contract_frame fuel (prog : core_program) imm (fr : source_frame)
                (w : source_world) gas =
    let env = core_program_environment prog in
    case dispatch env prog fr of
      DispatchRevert => (unconsumed_gas_result gas (ContractReverted [] w), NONE)
    | DispatchPanic n =>
        (unconsumed_gas_result gas (ContractReverted (panic_data n) w), NONE)
    | DispatchInvalid reason =>
        (unconsumed_gas_result gas (ContractInvalid reason), NONE)
    | DispatchCall p args kind =>
        let (r, image) = run_entry_frame fuel env p args fr w (SOME imm) 0 NONE kind gas in
        (r, SOME image)
End

Definition call_contract_with_gas_def:
  call_contract_with_gas fuel prog imm fr w gas =
    FST (call_contract_frame fuel prog imm fr w gas)
End

Theorem call_contract_with_gas_thm:
  call_contract_with_gas fuel prog imm fr w gas =
    let env = core_program_environment prog in
    case dispatch env prog fr of
      DispatchRevert => unconsumed_gas_result gas (ContractReverted [] w)
    | DispatchPanic n => unconsumed_gas_result gas (ContractReverted (panic_data n) w)
    | DispatchInvalid reason => unconsumed_gas_result gas (ContractInvalid reason)
    | DispatchCall p args kind =>
        run_entry_with_gas fuel env p args fr w (SOME imm) 0 NONE kind gas
Proof
  rw[call_contract_with_gas_def, call_contract_frame_def, run_entry_with_gas_def] >>
  CASE_TAC >> simp[pairTheory.UNCURRY]
QED

Definition call_contract_def:
  call_contract fuel prog imm fr w =
    call_contract_with_gas fuel prog imm fr w []
End

(* The creation transaction's frame of a contract, from a world in which its
 * account exists with no storage and holds the value sent. The constructor's
 * encoded arguments are supplied in the input frame and decoded before its
 * call_data is cleared: creation reads arguments from initcode, while msg.data
 * is empty. A creation sent value reverts unless the constructor is payable,
 * and arguments the decoder rejects revert. The immutables start at zero in
 * their reserved words, and a successful creation yields their values. Memory above the scratch space
 * holds a word for each immutable, then, for a constructor with parameters,
 * the copied arguments, so both the decoder and the constructor allocate
 * above them. A constructor without parameters gets no argument copy, as
 * in solc, and ignores any bytes after its initcode.
 *)
Definition deploy_contract_frame_def:
  deploy_contract_frame fuel (prog : core_program) (fr : source_frame)
                  (w : source_world) gas =
    let env = core_program_environment prog in
    case prog.creation_procedure of
      NONE => (unconsumed_gas_result gas (ContractInvalid "no creation procedure"), NONE)
    | SOME (f, payable) =>
        if ¬payable ∧ fr.call_value ≠ 0 then
          (unconsumed_gas_result gas (ContractReverted [] w), NONE)
        else
        case lookup_procedure env f of
          NONE => (unconsumed_gas_result gas (ContractInvalid "unknown procedure"), NONE)
        | SOME p =>
            let reserved = 32 * LENGTH prog.immutables +
                           (if p.parameters = [] then 0
                            else 32 * ((LENGTH fr.call_data + 31) DIV 32)) in
            case decode_arguments env (MAP SND p.parameters) fr.call_data 0
              (128 + reserved) of
              INR (PanicCompletion n) =>
                (unconsumed_gas_result gas (ContractReverted (panic_data n) w), NONE)
            | INR (InvalidCompletion reason) =>
                (unconsumed_gas_result gas (ContractInvalid reason), NONE)
            | INR _ => (unconsumed_gas_result gas (ContractReverted [] w), NONE)
            | INL args =>
                let (r, image) =
                  run_entry_frame fuel env p args (fr with call_data := []) w
                    NONE (32 * LENGTH prog.immutables)
                    (if p.parameters = [] then NONE else SOME fr.call_data)
                    CreationEntry gas in
                (r, SOME image)
End

Definition deploy_contract_with_gas_def:
  deploy_contract_with_gas fuel prog fr w gas =
    FST (deploy_contract_frame fuel prog fr w gas)
End

Theorem deploy_contract_with_gas_thm:
  deploy_contract_with_gas fuel prog fr w gas =
    case prog.creation_procedure of
      NONE => unconsumed_gas_result gas (ContractInvalid "no creation procedure")
    | SOME (f, payable) =>
        if ¬payable ∧ fr.call_value ≠ 0 then
          unconsumed_gas_result gas (ContractReverted [] w)
        else
        case lookup_procedure (core_program_environment prog) f of
          NONE => unconsumed_gas_result gas (ContractInvalid "unknown procedure")
        | SOME p =>
            case decode_arguments (core_program_environment prog)
              (MAP SND p.parameters) fr.call_data 0
              (128 + (32 * LENGTH prog.immutables +
                      if p.parameters = [] then 0
                      else 32 * ((LENGTH fr.call_data + 31) DIV 32))) of
              INR (PanicCompletion n) =>
                unconsumed_gas_result gas (ContractReverted (panic_data n) w)
            | INR (InvalidCompletion reason) =>
                unconsumed_gas_result gas (ContractInvalid reason)
            | INR _ => unconsumed_gas_result gas (ContractReverted [] w)
            | INL args =>
                run_entry_with_gas fuel (core_program_environment prog) p args
                  (fr with call_data := []) w
                  NONE (32 * LENGTH prog.immutables)
                  (if p.parameters = [] then NONE else SOME fr.call_data)
                  CreationEntry gas
Proof
  rw[deploy_contract_with_gas_def, deploy_contract_frame_def, run_entry_with_gas_def] >>
  rpt (CASE_TAC >> gvs[pairTheory.UNCURRY])
QED

Definition deploy_contract_def:
  deploy_contract fuel prog fr w = deploy_contract_with_gas fuel prog fr w []
End

(* A constructor without parameters decodes nothing, and solc copies no
 * argument buffer for it: bytes after the initcode change nothing, in
 * particular not where the free memory pointer starts. *)
Theorem deploy_contract_parameterless_ignores_arguments:
  prog.creation_procedure = SOME (f, payable) ∧
  lookup_procedure (core_program_environment prog) f = SOME p ∧
  p.parameters = [] ⇒
  deploy_contract fuel prog fr w =
  deploy_contract fuel prog (fr with call_data := []) w
Proof
  rw[deploy_contract_def, deploy_contract_with_gas_thm,
     solidityABITheory.decode_arguments_def, solidityABITheory.decode_input_def,
     solidityABITheory.decode_abi_arguments_def, solidityABITheory.abi_type_def,
     contractABITheory.head_lengths_def]
QED

Theorem call_contract_revert_restores_world:
  call_contract fuel prog imm fr w = ContractReverted data w' ⇒ w' = w
Proof
  rw[call_contract_def, call_contract_with_gas_thm,
     run_entry_with_gas_def, run_entry_frame_def, entry_output_def,
     unconsumed_gas_result_def,
     solidityStateTheory.finish_source_frame_def, AllCaseEqs()] >> simp[]
QED

(* An external call of an unsupported function, one the program does not
 * model, is refused: the call is invalid, never a return or a revert. *)
Theorem call_contract_unsupported:
  wf_core_program (core_program_environment prog) prog ∧
  4 ≤ LENGTH fr.call_data ∧
  lookup_external (TAKE 4 fr.call_data) prog.external_functions = SOME e ∧
  MEM e.external_procedure prog.unsupported_procedures ∧
  (e.payable ∨ fr.call_value = 0) ⇒
  call_contract fuel prog imm fr w = ContractInvalid "unknown procedure"
Proof
  rw[solidityCoreWfTheory.wf_core_program_def, listTheory.EVERY_MEM] >> first_x_assum drule >>
  rw[call_contract_def, call_contract_with_gas_thm,
     unconsumed_gas_result_def, dispatch_def]
QED

val () = cv_auto_trans lookup_external_def;
val () = cv_auto_trans dispatch_procedure_def;
val () = cv_auto_trans fallback_arguments_def;
val () = cv_auto_trans dispatch_def;
val () = cv_auto_trans fallback_output_def;
val () = cv_auto_trans entry_output_def;
val () = cv_auto_trans settle_source_world_def;
val memory_immutables_pre_def =
  cv_auto_trans_pre "memory_immutables_pre" memory_immutables_def;

Theorem memory_immutables_pre[cv_pre,local]:
  ∀env a l st. memory_immutables_pre env a l st
Proof
  Induct_on ‘l’ >> rw[Once memory_immutables_pre_def]
QED
val () = cv_auto_trans run_entry_frame_def;
val () = cv_auto_trans run_entry_with_gas_def;
val () = cv_auto_trans run_entry_def;
val () = cv_auto_trans unconsumed_gas_result_def;
val () = cv_auto_trans call_contract_frame_def;
val () = cv_auto_trans call_contract_with_gas_def;
val () = cv_auto_trans deploy_contract_frame_def;
val () = cv_auto_trans deploy_contract_with_gas_def;
val () = cv_auto_trans call_contract_def;
val () = cv_auto_trans deploy_contract_def;
