(* Smoke tests for the Yul evaluator, run by cv_eval: straight-line code and
 * memory, storage, a loop with a break, a call whose arguments must be
 * evaluated right to left, and the control outcomes.  The semantics test set
 * for the Solidity evaluator is solidityEvaluatorTest.
 *)
Theory yulEvaluatorTest
Ancestors
  yulEvaluator cv_string_fmap
Libs
  cv_transLib wordsLib

Definition yul_test_machine_def:
  yul_test_machine =
    <| accounts := empty_accounts; logs := []; self_address := 0w;
       call_value := 0w; call_data := []; memory := FEMPTY;
       memory_size := 0; scopes := [] |>
End

Definition run_def:
  run fuel code = run_yul fuel code yul_test_machine
End

val () = cv_auto_trans run_def;

(* mstore(0, add(2, 3)) return(0, 32) *)
Definition add_code_def:
  add_code =
    [YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 0w);
        YulBuiltin YAdd [YulLit (LitNumber 2w); YulLit (LitNumber 3w)]]);
     YulExprStmt (YulBuiltin YReturn
       [YulLit (LitNumber 0w); YulLit (LitNumber 32w)])]
End

val () = cv_auto_trans add_code_def;

(* sstore(7, 42) mstore(0, sload(7)) return(0, 32) *)
Definition store_code_def:
  store_code =
    [YulExprStmt (YulBuiltin YSStore
       [YulLit (LitNumber 7w); YulLit (LitNumber 42w)]);
     YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 0w); YulBuiltin YSLoad [YulLit (LitNumber 7w)]]);
     YulExprStmt (YulBuiltin YReturn
       [YulLit (LitNumber 0w); YulLit (LitNumber 32w)])]
End

val () = cv_auto_trans store_code_def;

(* let acc := 0
 * for { let i := 0 } lt(i, 3) { i := add(i, 1) } {
 *   acc := add(acc, i)
 *   if eq(i, 2) { break } }
 * mstore(0, acc) return(0, 32)
 * The loop leaves when i reaches 2, so acc is 0 + 1 + 2.
 *)
Definition loop_code_def:
  loop_code =
    [YulLet ["acc"] (SOME (YulLit (LitNumber 0w)));
     YulFor
       [YulLet ["i"] (SOME (YulLit (LitNumber 0w)))]
       (YulBuiltin YLt [YulName "i"; YulLit (LitNumber 3w)])
       [YulAssign ["i"] (YulBuiltin YAdd [YulName "i"; YulLit (LitNumber 1w)])]
       [YulAssign ["acc"] (YulBuiltin YAdd [YulName "acc"; YulName "i"]);
        YulIf (YulBuiltin YEq [YulName "i"; YulLit (LitNumber 2w)]) [YulBreak]];
     YulExprStmt (YulBuiltin YMStore [YulLit (LitNumber 0w); YulName "acc"]);
     YulExprStmt (YulBuiltin YReturn
       [YulLit (LitNumber 0w); YulLit (LitNumber 32w)])]
End

val () = cv_auto_trans loop_code_def;

(* function f(a, b) -> c { c := add(a, b) }
 * function g(a) -> b { b := a  sstore(0, a) }
 * let r := f(g(1), g(2))
 * mstore(0, r) mstore(32, sload(0)) return(0, 64)
 * Arguments are evaluated right to left, so g(2) stores before g(1) does and
 * slot 0 ends up holding 1; the sum in the returned word proves both ran.
 *)
Definition call_code_def:
  call_code =
    [YulFunction "f" ["a"; "b"] ["c"]
       [YulAssign ["c"] (YulBuiltin YAdd [YulName "a"; YulName "b"])];
     YulFunction "g" ["a"] ["b"]
       [YulAssign ["b"] (YulName "a");
        YulExprStmt (YulBuiltin YSStore [YulLit (LitNumber 0w); YulName "a"])];
     YulLet ["r"] (SOME (YulApply "f"
       [YulApply "g" [YulLit (LitNumber 1w)];
        YulApply "g" [YulLit (LitNumber 2w)]]));
     YulExprStmt (YulBuiltin YMStore [YulLit (LitNumber 0w); YulName "r"]);
     YulExprStmt (YulBuiltin YMStore
       [YulLit (LitNumber 32w); YulBuiltin YSLoad [YulLit (LitNumber 0w)]]);
     YulExprStmt (YulBuiltin YReturn
       [YulLit (LitNumber 0w); YulLit (LitNumber 64w)])]
End

val () = cv_auto_trans call_code_def;

(* for {} 1 {} {} -- never leaves the loop. *)
Definition spin_code_def:
  spin_code =
    [YulFor [] (YulLit (LitNumber 1w)) [] []]
End

val () = cv_auto_trans spin_code_def;

Definition revert_code_def:
  revert_code =
    [YulExprStmt (YulBuiltin YRevert
       [YulLit (LitNumber 0w); YulLit (LitNumber 0w)])]
End

val () = cv_auto_trans revert_code_def;

Definition leave_code_def:
  leave_code =
    [YulIf (YulLit (LitNumber 1w)) [YulLeave];
     YulExprStmt (YulBuiltin YRevert
       [YulLit (LitNumber 0w); YulLit (LitNumber 0w)])]
End

val () = cv_auto_trans leave_code_def;

Definition unbound_code_def:
  unbound_code = [YulLet ["x"] (SOME (YulName "y"))]
End

val () = cv_auto_trans unbound_code_def;

Theorem add_returns_five:
  (run 20 add_code).completion = YulReturn (word_to_bytes_be (5w : bytes32))
Proof
  CONV_TAC cv_eval
QED

(* The word stored is 32 bytes, so the active memory size is 32. *)
Theorem mstore_raises_memory_size:
  (run 20 add_code).machine.memory_size = 32
Proof
  CONV_TAC cv_eval
QED

Theorem storage_round_trips:
  (run 20 store_code).completion = YulReturn (word_to_bytes_be (42w : bytes32))
Proof
  CONV_TAC cv_eval
QED

Theorem loop_breaks_out:
  (run 20 loop_code).completion = YulReturn (word_to_bytes_be (3w : bytes32))
Proof
  CONV_TAC cv_eval
QED

Theorem call_arguments_are_evaluated_right_to_left:
  (run 20 call_code).completion =
  YulReturn (word_to_bytes_be (3w : bytes32) ++ word_to_bytes_be (1w : bytes32))
Proof
  CONV_TAC cv_eval
QED

Theorem spin_exhausts_fuel:
  (run 5 spin_code).completion = YulOutOfFuel
Proof
  CONV_TAC cv_eval
QED

(* More fuel, same syntax: a longer run reaches a real answer, and the answer
 * is what the shorter one would have given had it had the fuel. *)
Theorem fuel_only_bounds_steps:
  (run 20 call_code).completion ≠ YulOutOfFuel ∧
  (run 200 call_code).completion = (run 20 call_code).completion
Proof
  CONV_TAC cv_eval
QED

Theorem revert_returns_no_data:
  (run 20 revert_code).completion = YulRevert []
Proof
  CONV_TAC cv_eval
QED

(* leave ends the frame's code, so the revert after it never runs. *)
Theorem leave_leaves_the_code:
  (run 20 leave_code).completion = YulLeave
Proof
  CONV_TAC cv_eval
QED

Theorem unbound_name_is_invalid:
  (run 20 unbound_code).completion = YulInvalid "unbound name"
Proof
  CONV_TAC cv_eval
QED
