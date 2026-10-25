(* Differential runs of a source unit of the admitted subset on concrete
 * inputs: its deployed bytecode from the pinned compiler, called in
 * Verifereum, and its elaborated core, in the evaluator.
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

(* The evaluator run *)

Definition differential_state_def:
  differential_state = <|
    world := <| accounts := empty_accounts;
                transient := empty_transient_storage;
                logs := [] |>;
    frame := <| self_address := 0x1000w; code_address := 0x1000w;
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

Definition source_outcome_def:
  source_outcome u prog fuel name args =
    case unit_function u name of
      NONE => Diagnostic UnknownFunction
    | SOME f =>
        case callee_types f of
          NONE => Diagnostic UnknownFunction
        | SOME (params, rets) =>
            case argument_values params args of
              NONE => Diagnostic UnencodableArguments
            | SOME vs =>
                completion_outcome rets
                  (invoke_source fuel (core_program_environment [] prog)
                     (AstId f.fn_info.node_id) vs differential_state
                     []).completion
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
    from := 0x2000w; to := SOME 0x1000w; data := data; nonce := 0;
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

(* A call of the code deployed at 0x1000 from 0x2000. *)
Definition evm_outcome_def:
  evm_outcome code u name args =
    case function_types u name of
      NONE => Diagnostic UnknownFunction
    | SOME (params, rets) =>
        case argument_values params args of
          NONE => Diagnostic UnencodableArguments
        | SOME vs =>
            case call_data name params vs of
              NONE => Diagnostic UnencodableArguments
            | SOME data =>
                let accounts = update_account 0x1000w
                                 (empty_account_state with code := code)
                                 empty_accounts in
                case run_transaction (Collect empty_domain) F 1 []
                       differential_block accounts (differential_tx data) of
                  SOME (r, _) =>
                    (case r.result of
                       NONE => Returned r.output
                     | SOME Reverted => Reverted r.output
                     | SOME _ => Diagnostic ExceptionalHalt)
                | NONE => Diagnostic InvalidTransaction
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
End

Definition compare_outcomes_def:
  compare_outcomes expected evm src =
    if is_diagnostic evm ∨ is_diagnostic src then Inconclusive evm src
    else if evm ≠ src then Mismatch evm src
    else if evm ≠ expected then Unexpected evm expected
    else Agree evm
End

Definition differential_verdict_def:
  differential_verdict code u prog fuel name args e =
    compare_outcomes (expected_outcome u name e)
      (evm_outcome code u name args) (source_outcome u prog fuel name args)
End

Definition is_agreement_def:
  (is_agreement (Agree _) ⇔ T) ∧
  (is_agreement _ ⇔ F)
End

Definition differential_agrees_def:
  differential_agrees code u prog fuel name args e ⇔
    is_agreement (differential_verdict code u prog fuel name args e)
End

(* What an agreement establishes: both runs produce the expected outcome,
 * which is a return or a revert, never a diagnostic.
 *)
Theorem differential_agrees_outcomes:
  differential_agrees code u prog fuel name args e ⇒
  ¬is_diagnostic (expected_outcome u name e) ∧
  evm_outcome code u name args = expected_outcome u name e ∧
  source_outcome u prog fuel name args = expected_outcome u name e
Proof
  rw[differential_agrees_def, differential_verdict_def, compare_outcomes_def,
     is_agreement_def] >> gvs[]
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
val () = cv_auto_trans source_outcome_def;
val () = cv_auto_trans call_data_def;
val () = cv_auto_trans evm_outcome_def;
val () = cv_auto_trans expected_outcome_def;
val () = cv_auto_trans compare_outcomes_def;
val () = cv_auto_trans differential_verdict_def;
val () = cv_auto_trans is_agreement_def;
val () = cv_auto_trans differential_agrees_def;
