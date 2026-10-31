(* Differential runs of a source unit of the admitted subset on concrete
 * inputs: its deployed bytecode from the pinned compiler, called in
 * Verifereum, and its elaborated core, in the evaluator.
 *
 * Both runs start from the same storage of the contract account, given as
 * slot/value pairs, and are observed by their outcome and by the contract's
 * complete committed storage, including unlisted hashed slots. Listed slots
 * from the layout/initial/expected storage are retained for diagnostics and
 * the existing observation interface; agreement additionally checks exact
 * storage-function equality through Verifereum's sparse cv representation.
 *
 * Encoding convention: both runs are observed as ABI-encoded data. A return
 * is the encoding of the declared return types; a panic is the revert data
 * Panic(uint256), selector 0x4e487b71; any other revert is its raw data.
 * Inputs are written as integers, booleans or byte strings and are typed by
 * the function's parameters; an input outside its type is a diagnostic, not a
 * call.
 *
 * Diagnostics are never agreement: an unknown function, an input or result
 * that cannot be encoded, fuel exhaustion, an invalid completion, an
 * exceptional halt of the bytecode and an invalid transaction are distinct
 * outcomes, and a comparison involving one is inconclusive. Import rejection,
 * elaboration rejection and an invalid core are reported per unit by
 * solidityDifferentialLib before any call is made.
 *)
Theory solidityDifferential
Ancestors
  solidityStorage
  solidityElaborate contractABI keccak vfmCompute
Libs
  cv_transLib wordsLib intLib

(* Inputs *)

Datatype:
  argument = IntArg int | BoolArg bool | BytesArg (byte list)
End

Definition argument_scalar_def:
  (argument_scalar (IntArg i) = IntegerValue i) ∧
  (argument_scalar (BoolArg b) = BoolValue b) ∧
  (argument_scalar (BytesArg bs) = BytesValue bs)
End

(* An address is written as an integer or as 20 bytes. *)
Definition argument_value_def:
  (argument_value (AddressT _) (IntArg i) =
    if 0 ≤ i ∧ i < &(2 ** 160) then
      SOME (ScalarValue (AddressValue (n2w (Num i))))
    else NONE) ∧
  (argument_value (AddressT _) (BytesArg bs) =
    if LENGTH bs = 20 then
      SOME (ScalarValue (AddressValue (n2w (num_of_be_bytes bs))))
    else NONE) ∧
  (argument_value ty a =
    if elementary_scalar_has_type ty (argument_scalar a) then
      SOME (ScalarValue (argument_scalar a))
    else NONE)
End

Definition argument_values_def:
  (argument_values [] [] = SOME []) ∧
  (argument_values (ty :: tys) (a :: as) =
    case (argument_value ty a, argument_values tys as) of
      (SOME v, SOME vs) => SOME (v :: vs)
    | _ => NONE) ∧
  (argument_values _ _ = NONE)
End

(* ABI encoding of elementary values *)

Definition abi_type_def:
  (abi_type (UintT n) = Uint n) ∧
  (abi_type (IntT n) = Int n) ∧
  (abi_type BoolT = Bool) ∧
  (abi_type (AddressT _) = Address) ∧
  (abi_type (FixedBytesT n) = Bytes (SOME n)) ∧
  (abi_type _ = Tuple [])
End

Definition abi_value_def:
  (abi_value (UintT _) (ScalarValue (IntegerValue i)) = SOME (NumV (Num i))) ∧
  (abi_value (IntT _) (ScalarValue (IntegerValue i)) = SOME (IntV i)) ∧
  (abi_value BoolT (ScalarValue (BoolValue b)) =
    SOME (NumV (if b then 1 else 0))) ∧
  (abi_value (AddressT _) (ScalarValue (AddressValue a)) =
    SOME (NumV (w2n a))) ∧
  (abi_value (FixedBytesT _) (ScalarValue (BytesValue bs)) = SOME (BytesV bs)) ∧
  (abi_value _ _ = NONE)
End

Definition abi_values_def:
  (abi_values [] [] = SOME []) ∧
  (abi_values (ty :: tys) (v :: vs) =
    case (abi_value ty v, abi_values tys vs) of
      (SOME a, SOME as) => SOME (a :: as)
    | _ => NONE) ∧
  (abi_values _ _ = NONE)
End

(* Outcomes *)

Datatype:
  diagnostic =
    UnknownFunction
  | UnencodableArguments
  | UnencodableResult
  | OutOfFuel
  | InvalidCompletion
  | ExceptionalHalt
  | InvalidTransaction
End

Datatype:
  call_outcome = Returned (byte list) | Reverted (byte list) | Diagnostic diagnostic
End

Definition is_diagnostic_def:
  (is_diagnostic (Diagnostic _) ⇔ T) ∧
  (is_diagnostic _ ⇔ F)
End

Definition returned_def:
  returned tys vs = Returned (enc (Tuple tys) (ListV vs))
End

Definition panic_data_def:
  panic_data n = [0x4Ew; 0x48w; 0x7Bw; 0x71w] ++ enc (Uint 256) (NumV n)
End

(* The ABI encoding of values of the given types. *)
Definition encoded_values_def:
  encoded_values tys vs =
    case abi_values tys vs of
      SOME avs => SOME (enc (Tuple (MAP abi_type tys)) (ListV avs))
    | NONE => NONE
End

(* Functions of the unit's contract *)

Definition unit_function_def:
  unit_function u name =
    case u.unit_contracts of
      c :: _ =>
        (case FILTER (λf. f.fn_name = name) c.contract_functions of
           f :: _ => SOME f
         | [] => NONE)
    | [] => NONE
End

Definition function_types_def:
  function_types u name =
    case unit_function u name of
      SOME f => callee_types f
    | NONE => NONE
End

(* Storage *)

Definition contract_address_def:
  contract_address = 0x1000w : address
End

Definition seed_storage_def:
  (seed_storage [] = empty_storage) ∧
  (seed_storage ((k, v) :: kvs) =
    update_storage (n2w k) (n2w v) (seed_storage kvs))
End

(* The contract, with its code and initial storage, and no other account. *)
Definition contract_accounts_def:
  contract_accounts code storage =
    update_account contract_address
      (empty_account_state with <| code := code;
                                   storage := seed_storage storage |>)
      empty_accounts
End

Definition observed_slots_def:
  observed_slots (prog : core_program) storage final =
    nub
      (MAP (λv. w2n v.state_slot) prog.state_variables ++ MAP FST storage ++
       MAP FST final)
End

Definition storage_values_def:
  storage_values st slots = MAP (λk. (k, w2n (lookup_storage (n2w k) st))) slots
End

Definition storage_at_def:
  storage_at accounts slots =
    storage_values (lookup_account contract_address accounts).storage slots
End

(* A projection for diagnostics and the retained listed-slot interface. *)
Definition project_observation_def:
  project_observation slots (outcome, st) =
    (outcome, case st of NONE => [] | SOME store => storage_values store slots)
End

(* A listed slot ends with its listed value, any other with its initial one. *)
Definition expected_storage_def:
  expected_storage storage final slots =
    MAP (λk. (k, case ALOOKUP final k of
                   SOME v => v
                 | NONE => (case ALOOKUP storage k of SOME v => v | NONE => 0)))
      slots
End

(* The evaluator run *)

Definition differential_state_def:
  differential_state accounts = <|
    world := <| accounts := accounts;
                transient := empty_transient_storage;
                logs := [] |>;
    frame := <| self_address := contract_address;
                code_address := contract_address;
                sender_address := 0x2000w; call_value := 0; call_data := [];
                static_context := F |>;
    scopes := [];
    heap := FEMPTY;
    next_heap_id := 0;
    targets := FEMPTY
  |>
End

Definition completion_outcome_def:
  completion_outcome rets c =
    case c of
      ReturnCompletion vs =>
        (case encoded_values rets vs of
           SOME bs => Returned bs
         | NONE => Diagnostic UnencodableResult)
    | PanicCompletion n => Reverted (panic_data n)
    | RevertCompletion bs => Reverted bs
    | FuelExhausted => Diagnostic OutOfFuel
    | _ => Diagnostic InvalidCompletion
End

(* The world a frame commits: a revert or panic restores the initial one. *)
Definition committed_world_def:
  committed_world initial final c =
    case finish_source_frame initial final c of
      FrameSuccess _ w => SOME w
    | FrameRevert _ w => SOME w
    | FramePanic _ w => SOME w
    | _ => NONE
End

(* The outcome and complete committed contract storage of the evaluator run. *)
Definition source_execution_def:
  source_execution code u prog fuel name args storage =
    case unit_function u name of
      NONE => (Diagnostic UnknownFunction, NONE)
    | SOME f =>
        case callee_types f of
          NONE => (Diagnostic UnknownFunction, NONE)
        | SOME (params, rets) =>
            case argument_values params args of
              NONE => (Diagnostic UnencodableArguments, NONE)
            | SOME vs =>
                let st = differential_state (contract_accounts code storage) in
                let r = invoke_source fuel (core_program_environment prog)
                          (AstId f.fn_info.node_id) vs st [] in
                (completion_outcome rets r.completion,
                 case committed_world st.world r.state.world r.completion of
                   SOME w => SOME (lookup_account contract_address w.accounts).storage
                 | NONE => NONE)
End

Definition source_observation_def:
  source_observation code u prog fuel name args storage slots =
    project_observation slots (source_execution code u prog fuel name args storage)
End

(* The bytecode run *)

Definition differential_block_def:
  differential_block = <|
    baseFeePerGas := 0; excessBlobGas := 0; gasUsed := 0; blobGasUsed := 0;
    number := 1; timeStamp := 1; coinBase := 0w; gasLimit := 30000000;
    prevRandao := 0w; hash := 0w; parentBeaconBlockRoot := 0w;
    stateRoot := 0w; transactions := []; withdrawals := [];
    requestsHash := 0w; withdrawalsRoot := 0w
  |>
End

Definition differential_tx_def:
  differential_tx data = <|
    from := 0x2000w; to := SOME contract_address; data := data; nonce := 0;
    value := 0; gasLimit := 10000000; gasPrice := 0; accessList := [];
    blobVersionedHashes := []; maxFeePerBlobGas := NONE; maxFeePerGas := NONE;
    authorizationList := []
  |>
End

Definition call_data_def:
  call_data name params vs =
    case encoded_values params vs of
      SOME bs => SOME (function_selector name (MAP abi_type params) ++ bs)
    | NONE => NONE
End

(* A call of the code deployed at 0x1000 from 0x2000: its outcome, and the
 * final storage at the slots.
 *)
Definition evm_execution_def:
  evm_execution code u name args storage =
    case function_types u name of
      NONE => (Diagnostic UnknownFunction, NONE)
    | SOME (params, rets) =>
        case argument_values params args of
          NONE => (Diagnostic UnencodableArguments, NONE)
        | SOME vs =>
            case call_data name params vs of
              NONE => (Diagnostic UnencodableArguments, NONE)
            | SOME data =>
                case run_transaction (Collect empty_domain) F 1 []
                       differential_block (contract_accounts code storage)
                       (differential_tx data) of
                  SOME (r, accounts) =>
                    (case r.result of
                       NONE => (Returned r.output, SOME (lookup_account contract_address accounts).storage)
                     | SOME Reverted =>
                         (Reverted r.output, SOME (lookup_account contract_address accounts).storage)
                     | SOME _ => (Diagnostic ExceptionalHalt, NONE))
                | NONE => (Diagnostic InvalidTransaction, NONE)
End

Definition evm_observation_def:
  evm_observation code u name args storage slots =
    project_observation slots (evm_execution code u name args storage)
End

(* Expected outcomes *)

Datatype:
  expectation =
    ExpectReturn (argument list) | ExpectPanic num | ExpectRevert (byte list)
End

Definition expected_outcome_def:
  expected_outcome u name e =
    case e of
      ExpectReturn results =>
        (case function_types u name of
           NONE => Diagnostic UnknownFunction
         | SOME (params, rets) =>
             case argument_values rets results of
               NONE => Diagnostic UnencodableResult
             | SOME vs =>
                 case encoded_values rets vs of
                   SOME bs => Returned bs
                 | NONE => Diagnostic UnencodableResult)
    | ExpectPanic n => Reverted (panic_data n)
    | ExpectRevert bs => Reverted bs
End

(* Comparison *)

Datatype:
  verdict =
    Agree call_outcome
    (* bytecode, source *)
  | Mismatch call_outcome call_outcome
    (* the outcome both runs agree on, the expected one *)
  | Unexpected call_outcome call_outcome
    (* bytecode, source, at least one a diagnostic *)
  | Inconclusive call_outcome call_outcome
    (* final storage: bytecode, source *)
  | StorageMismatch ((num # num) list) ((num # num) list)
    (* final storage: the one both runs agree on, the expected one *)
  | StorageUnexpected ((num # num) list) ((num # num) list)
End

Definition compare_observations_def:
  compare_observations (expected, expected_st) (evm, evm_st) (src, src_st) =
    if is_diagnostic evm ∨ is_diagnostic src then Inconclusive evm src
    else if evm ≠ src then Mismatch evm src
    else if evm ≠ expected then Unexpected evm expected
    else if evm_st ≠ src_st then StorageMismatch evm_st src_st
    else if evm_st ≠ expected_st then StorageUnexpected evm_st expected_st
    else Agree evm
End

Definition differential_verdict_def:
  differential_verdict code u prog fuel name args storage e final =
    let slots = observed_slots prog storage final in
    let evm_run = evm_execution code u name args storage in
    let src_run = source_execution code u prog fuel name args storage in
    let evm = project_observation slots evm_run in
    let src = project_observation slots src_run in
    case compare_observations
      (expected_outcome u name e, expected_storage storage final slots) evm src of
      Agree outcome =>
        if SND evm_run ≠ SND src_run then StorageMismatch (SND evm) (SND src)
        else if SND evm_run ≠ SOME (seed_storage (final ++ storage)) then
          StorageUnexpected (SND evm) (expected_storage storage final slots)
        else Agree outcome
    | other => other
End

Definition is_agreement_def:
  (is_agreement (Agree _) ⇔ T) ∧
  (is_agreement _ ⇔ F)
End

Definition differential_agrees_def:
  differential_agrees code u prog fuel name args storage e final ⇔
    is_agreement
      (differential_verdict code u prog fuel name args storage e final)
End

Theorem compare_observations_agree:
  is_agreement (compare_observations x y z) ⇒
  ¬is_diagnostic (FST x) ∧ y = x ∧ z = x
Proof
  PairCases_on ‘x’ >> PairCases_on ‘y’ >> PairCases_on ‘z’ >>
  simp[compare_observations_def] >> rpt IF_CASES_TAC >>
  gvs[is_agreement_def]
QED

Theorem complete_storage_check_agreement[local]:
  is_agreement
    (case verdict of
       Agree outcome =>
         if evm_st ≠ src_st then StorageMismatch evm_slots src_slots
         else if src_st ≠ expected_st then StorageUnexpected evm_slots expected_slots
         else Agree outcome
     | other => other) ⇒
  is_agreement verdict
Proof
  Cases_on ‘verdict’ >> simp[is_agreement_def] >>
  rpt IF_CASES_TAC >> simp[is_agreement_def]
QED

(* What an agreement establishes: both runs produce the expected outcome,
 * which is a return or a revert, never a diagnostic, and the expected final
 * storage at the observed slots.
 *)
Theorem differential_agrees_outcomes:
  differential_agrees code u prog fuel name args storage e final ∧
  slots = observed_slots prog storage final ⇒
  ¬is_diagnostic (expected_outcome u name e) ∧
  evm_observation code u name args storage slots =
    (expected_outcome u name e, expected_storage storage final slots) ∧
  source_observation code u prog fuel name args storage slots =
    (expected_outcome u name e, expected_storage storage final slots)
Proof
  rw[differential_agrees_def, differential_verdict_def,
     evm_observation_def, source_observation_def] >>
  drule complete_storage_check_agreement >> strip_tac >>
  drule compare_observations_agree >> simp[]
QED

val () = cv_auto_trans argument_scalar_def;
val () = cv_auto_trans solidityCoreWfTheory.elementary_scalar_has_type_def;
val () = cv_auto_trans argument_value_def;
val () = cv_auto_trans argument_values_def;
val () = cv_auto_trans abi_type_def;
val () = cv_auto_trans abi_value_def;
val () = cv_auto_trans abi_values_def;
val () = cv_auto_trans is_diagnostic_def;
val () = cv_auto_trans panic_data_def;
val () = cv_auto_trans returned_def;
val () = cv_auto_trans encoded_values_def;
val () = cv_auto_trans unit_function_def;
val () = cv_auto_trans function_types_def;
val () = cv_auto_trans completion_outcome_def;
val () = cv_auto_trans seed_storage_def;
val () = cv_auto_trans contract_accounts_def;
val () = cv_auto_trans listTheory.nub_def;
val () = cv_auto_trans observed_slots_def;
val () = cv_auto_trans storage_values_def;
val () = cv_auto_trans storage_at_def;
val () = cv_auto_trans project_observation_def;
val () = cv_auto_trans expected_storage_def;
val () = cv_auto_trans committed_world_def;
val () = cv_auto_trans source_execution_def;
val () = cv_auto_trans source_observation_def;
val () = cv_auto_trans call_data_def;
val () = cv_auto_trans evm_execution_def;
val () = cv_auto_trans evm_observation_def;
val () = cv_auto_trans expected_outcome_def;
val () = cv_auto_trans compare_observations_def;
val () = cv_auto_trans differential_verdict_def;
val () = cv_auto_trans is_agreement_def;
val () = cv_auto_trans differential_agrees_def;
