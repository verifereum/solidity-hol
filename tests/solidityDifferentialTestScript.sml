(* testdata/frontend/pure_core.sol run two ways on the same inputs: its
 * deployed bytecode from the pinned compiler, called in Verifereum, and its
 * elaborated core, in the evaluator. Both outcomes are ABI-encoded and must
 * be equal: return data, or revert data, with a panic as Panic(uint256).
 *)
Theory solidityDifferentialTest
Ancestors
  solidityElaborateTest contractABI keccak vfmCompute
Libs
  solidityImportLib cv_transLib wordsLib intLib

(* Read by holbuild's dependency scanner, which stages the fixture. *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../testdata/frontend/expected/pure_core.json"]

Definition pure_core_code_def:
  pure_core_code = REVERSE $ hex_to_rev_bytes [] $
    ^(stringSyntax.fromMLstring
        (artifact_deployed_bytecode
           "../testdata/frontend/expected/pure_core.json"
           "testdata/frontend/pure_core.sol" "PureCore"))
End

val () = cv_trans_deep_embedding EVAL pure_core_code_def;

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
  call_outcome = Returned (byte list) | Reverted (byte list) | Diagnostic string
End

Definition returned_def:
  returned tys vs = Returned (enc (Tuple tys) (ListV vs))
End

Definition panic_data_def:
  panic_data n = [0x4Ew; 0x48w; 0x7Bw; 0x71w] ++ enc (Uint 256) (NumV n)
End

Definition function_types_def:
  function_types name =
    case pure_core.unit_contracts of
      c :: _ =>
        (case FILTER (λf. f.fn_name = name) c.contract_functions of
           f :: _ => callee_types f
         | [] => NONE)
    | [] => NONE
End

(* The evaluator on integer arguments; fuel exhaustion and invalid
 * completions are diagnostics, never agreement with the bytecode.
 *)
Definition source_outcome_def:
  source_outcome name args =
    case function_types name of
      NONE => Diagnostic "unknown function"
    | SOME (params, rets) =>
        case run_function 1000 name args of
          ReturnCompletion vs =>
            (case abi_values rets vs of
               SOME avs => returned (MAP abi_type rets) avs
             | NONE => Diagnostic "unencodable result")
        | PanicCompletion n => Reverted (panic_data n)
        | RevertCompletion bs => Reverted bs
        | FuelExhausted => Diagnostic "fuel exhausted"
        | _ => Diagnostic "invalid completion"
End

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

(* A call of the deployed bytecode with the ABI-encoded arguments. *)
Definition evm_outcome_def:
  evm_outcome name args =
    case function_types name of
      NONE => Diagnostic "unknown function"
    | SOME (params, rets) =>
        case abi_values params (MAP iv args) of
          NONE => Diagnostic "unencodable arguments"
        | SOME avs =>
            let tys = MAP abi_type params in
            let accounts = update_account 0x1000w
                             (empty_account_state with code := pure_core_code)
                             empty_accounts in
            case run_transaction (Collect empty_domain) F 1 []
                   differential_block accounts
                   (differential_tx (function_selector name tys ++
                                     enc (Tuple tys) (ListV avs))) of
              SOME (r, _) =>
                (case r.result of
                   NONE => Returned r.output
                 | SOME Reverted => Reverted r.output
                 | SOME _ => Diagnostic "exceptional halt")
            | NONE => Diagnostic "invalid transaction"
End

(* The common outcome, if the two runs agree. *)
Definition differential_def:
  differential name args =
    let outcome = evm_outcome name args in
    if outcome = source_outcome name args then SOME outcome else NONE
End

val () = cv_auto_trans differential_def;

(* Evaluates the one call of the named outcome function, so that the bytecode
 * run, the evaluator run and the comparison are separate proof steps.
 *)
fun cv_eval_call name =
  ONCE_DEPTH_CONV (fn t =>
    let val (f, _) = strip_comb t in
      if is_const f andalso fst (dest_const f) = name then cv_eval t
      else NO_CONV t
    end)

Theorem add_returns:
  differential "add" [2; 3] = SOME (returned [Uint 8] [NumV 5])
Proof
  rewrite_tac [differential_def] >>
  CONV_TAC (cv_eval_call "evm_outcome") >>
  CONV_TAC (cv_eval_call "source_outcome") >>
  CONV_TAC cv_eval
QED

Theorem add_overflow_panics:
  differential "add" [200; 100] = SOME (Reverted (panic_data 0x11))
Proof
  rewrite_tac [differential_def] >>
  CONV_TAC (cv_eval_call "evm_outcome") >>
  CONV_TAC (cv_eval_call "source_outcome") >>
  CONV_TAC cv_eval
QED

Theorem unchecked_add_wraps:
  differential "wrappingAdd" [200; 100] = SOME (returned [Uint 8] [NumV 44])
Proof
  rewrite_tac [differential_def] >>
  CONV_TAC (cv_eval_call "evm_outcome") >>
  CONV_TAC (cv_eval_call "source_outcome") >>
  CONV_TAC cv_eval
QED

Theorem while_break:
  differential "count" [100] =
  SOME (returned [Uint 256; Uint 256] [NumV 3; NumV 6])
Proof
  rewrite_tac [differential_def] >>
  CONV_TAC (cv_eval_call "evm_outcome") >>
  CONV_TAC (cv_eval_call "source_outcome") >>
  CONV_TAC cv_eval
QED

Theorem for_continue_increments:
  differential "sum" [5] = SOME (returned [Uint 256] [NumV 8])
Proof
  rewrite_tac [differential_def] >>
  CONV_TAC (cv_eval_call "evm_outcome") >>
  CONV_TAC (cv_eval_call "source_outcome") >>
  CONV_TAC cv_eval
QED

Theorem do_while_loops:
  differential "doubleUntil" [7] = SOME (returned [Uint 256] [NumV 8])
Proof
  rewrite_tac [differential_def] >>
  CONV_TAC (cv_eval_call "evm_outcome") >>
  CONV_TAC (cv_eval_call "source_outcome") >>
  CONV_TAC cv_eval
QED

Theorem recursion:
  differential "fact" [5] = SOME (returned [Uint 256] [NumV 120])
Proof
  rewrite_tac [differential_def] >>
  CONV_TAC (cv_eval_call "evm_outcome") >>
  CONV_TAC (cv_eval_call "source_outcome") >>
  CONV_TAC cv_eval
QED

Theorem multiple_returns:
  differential "divmod" [17; 5] =
  SOME (returned [Uint 256; Uint 256] [NumV 3; NumV 2])
Proof
  rewrite_tac [differential_def] >>
  CONV_TAC (cv_eval_call "evm_outcome") >>
  CONV_TAC (cv_eval_call "source_outcome") >>
  CONV_TAC cv_eval
QED

Theorem division_by_zero_panics:
  differential "divmod" [1; 0] = SOME (Reverted (panic_data 0x12))
Proof
  rewrite_tac [differential_def] >>
  CONV_TAC (cv_eval_call "evm_outcome") >>
  CONV_TAC (cv_eval_call "source_outcome") >>
  CONV_TAC cv_eval
QED

Theorem tuple_assignment:
  differential "swap" [] =
  SOME (returned [Uint 256; Uint 256] [NumV 2; NumV 3])
Proof
  rewrite_tac [differential_def] >>
  CONV_TAC (cv_eval_call "evm_outcome") >>
  CONV_TAC (cv_eval_call "source_outcome") >>
  CONV_TAC cv_eval
QED

Theorem locals_and_tuple_declarations:
  differential "locals" [10] = SOME (returned [Uint 256] [NumV 10])
Proof
  rewrite_tac [differential_def] >>
  CONV_TAC (cv_eval_call "evm_outcome") >>
  CONV_TAC (cv_eval_call "source_outcome") >>
  CONV_TAC cv_eval
QED

Theorem narrowing_conversion:
  differential "narrow" [300] =
  SOME (returned [Uint 8; Bool] [NumV 44; NumV 0])
Proof
  rewrite_tac [differential_def] >>
  CONV_TAC (cv_eval_call "evm_outcome") >>
  CONV_TAC (cv_eval_call "source_outcome") >>
  CONV_TAC cv_eval
QED

Theorem negate_overflow_panics:
  differential "negate" [-128] = SOME (Reverted (panic_data 0x11))
Proof
  rewrite_tac [differential_def] >>
  CONV_TAC (cv_eval_call "evm_outcome") >>
  CONV_TAC (cv_eval_call "source_outcome") >>
  CONV_TAC cv_eval
QED

Theorem negate_returns:
  differential "negate" [5] = SOME (returned [Int 8] [IntV (-5)])
Proof
  rewrite_tac [differential_def] >>
  CONV_TAC (cv_eval_call "evm_outcome") >>
  CONV_TAC (cv_eval_call "source_outcome") >>
  CONV_TAC cv_eval
QED

Theorem and_skips_division:
  differential "guardedDivide" [0] = SOME (returned [Bool] [NumV 0])
Proof
  rewrite_tac [differential_def] >>
  CONV_TAC (cv_eval_call "evm_outcome") >>
  CONV_TAC (cv_eval_call "source_outcome") >>
  CONV_TAC cv_eval
QED

Theorem and_division_panics:
  differential "badDivide" [0] = SOME (Reverted (panic_data 0x12))
Proof
  rewrite_tac [differential_def] >>
  CONV_TAC (cv_eval_call "evm_outcome") >>
  CONV_TAC (cv_eval_call "source_outcome") >>
  CONV_TAC cv_eval
QED

Theorem or_skips_increment:
  differential "shortCircuit" [10] =
  SOME (returned [Bool; Uint 256] [NumV 1; NumV 0])
Proof
  rewrite_tac [differential_def] >>
  CONV_TAC (cv_eval_call "evm_outcome") >>
  CONV_TAC (cv_eval_call "source_outcome") >>
  CONV_TAC cv_eval
QED

Theorem or_runs_increment:
  differential "shortCircuit" [1] =
  SOME (returned [Bool; Uint 256] [NumV 1; NumV 1])
Proof
  rewrite_tac [differential_def] >>
  CONV_TAC (cv_eval_call "evm_outcome") >>
  CONV_TAC (cv_eval_call "source_outcome") >>
  CONV_TAC cv_eval
QED

Theorem left_operand_panics_first:
  differential "panicOrder" [0] = SOME (Reverted (panic_data 0x11))
Proof
  rewrite_tac [differential_def] >>
  CONV_TAC (cv_eval_call "evm_outcome") >>
  CONV_TAC (cv_eval_call "source_outcome") >>
  CONV_TAC cv_eval
QED

Theorem left_argument_panics_first:
  differential "argumentOrder" [0] = SOME (Reverted (panic_data 0x11))
Proof
  rewrite_tac [differential_def] >>
  CONV_TAC (cv_eval_call "evm_outcome") >>
  CONV_TAC (cv_eval_call "source_outcome") >>
  CONV_TAC cv_eval
QED

Theorem compound_assignment_reads_after_rhs:
  differential "compoundOrder" [1] = SOME (returned [Uint 256] [NumV 10])
Proof
  rewrite_tac [differential_def] >>
  CONV_TAC (cv_eval_call "evm_outcome") >>
  CONV_TAC (cv_eval_call "source_outcome") >>
  CONV_TAC cv_eval
QED
