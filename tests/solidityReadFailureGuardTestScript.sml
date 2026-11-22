(* Calls where an input read fails after reaching at or above the free memory
 * pointer, or where an event hash preimage moved the free memory pointer below
 * what the event read: bytecode outcomes are checked independently, and the
 * source model must fail closed instead of surfacing any read failure. *)
Theory solidityReadFailureGuardTest
Ancestors solidityCoreWf solidityDifferentialCorpus_read_failure_guards
Libs solidityBytecodeLib cv_transLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [
  "../SOLIDITY_PIN",
  "../profiles/solc-0.8.37-via-ir-osaka.json",
  "../testdata/differential/read_failure_guards.sol",
  "../testdata/differential/expected/read_failure_guards.json",
  "../testdata/differential/fail_closed/read_failure_guards.json"
]

val () = solidityBytecodeLib.run_suite_file
  {root = "..", suite_file = "testdata/differential/fail_closed/read_failure_guards.json"}

fun rejected_case name =
  let
    open solidityBytecodeLib
    val suite = JSONParser.parseFile
      "../testdata/differential/fail_closed/read_failure_guards.json"
    val c = valOf (List.find (fn c => string_field c "name" = name)
                    (array_field suite "cases"))
  in
    case_term {peer = “[] : byte list”, libraries = “[] : (address # byte list) list”}
      {names = [], refs = “[] : (num # num list) list”}
      (call_input (fn () => “[] : byte list”) c) c
  end;

(* The reason a call stops with, which `contract_observation` drops: every
 * fail-closed path shows as `(Diagnostic InvalidCompletion, NONE, [])`, so an
 * observation alone cannot say which guard stopped the run. This is the call
 * branch of `source_frame_execution_at` (the same transaction, frame and
 * world), keeping the reason of a `ContractInvalid`. *)
Definition source_failure_reason_def:
  source_failure_reason code u prog fuel c =
    case (input_call u c.case_input, case_immutable_values u c.case_immutables) of
      (INR (data, _), SOME imm) =>
        let a = case_address c in
        let fr0 = differential_frame c.case_sender c.case_value data in
        let fr = fr0 with <| self_address := a; code_address := a;
                             tx_params := fr0.tx_params with gasPrice :=
                               (differential_tx c.case_sender c.case_value []).gasPrice |> in
        let pre = case_accounts (patch_immutables c.case_immutable_refs imm code)
                    c.case_storage c.case_sender
                    c.case_peer_code c.case_peer_storage c.case_libraries in
        let w = differential_world (transfer_value c.case_sender a c.case_value pre)
                  with original := pre in
        (case FST (call_contract_frame fuel prog
                     (FEMPTY |++ MAP (λ(x, s, _). (x, s)) imm) fr w
                     (MAP GasLeftObservation c.case_gas)) of
           ContractInvalid reason => SOME reason
         | _ => NONE)
    | _ => NONE
End

val () = cv_auto_trans source_failure_reason_def;

Theorem encoder_overlap_return_fails_closed:
  (source_execution bytecode_rejected_read_failure_guards_code
    corpus_read_failure_guards_unit corpus_read_failure_guards_program 1000
    ^(rejected_case "encoder_overlap_return") =
   (Diagnostic InvalidCompletion, NONE, [])) ∧
  source_failure_reason bytecode_rejected_read_failure_guards_code
    corpus_read_failure_guards_unit corpus_read_failure_guards_program 1000
    ^(rejected_case "encoder_overlap_return") = SOME "unsupported: encoder input at or above the free memory pointer"
Proof
  CONV_TAC cv_eval
QED

Theorem encoder_overlap_first_fails_closed:
  (source_execution bytecode_rejected_read_failure_guards_code
    corpus_read_failure_guards_unit corpus_read_failure_guards_program 1000
    ^(rejected_case "encoder_overlap_first") =
   (Diagnostic InvalidCompletion, NONE, [])) ∧
  source_failure_reason bytecode_rejected_read_failure_guards_code
    corpus_read_failure_guards_unit corpus_read_failure_guards_program 1000
    ^(rejected_case "encoder_overlap_first") = SOME "unsupported: encoder input at or above the free memory pointer"
Proof
  CONV_TAC cv_eval
QED

Theorem encoder_earlier_valid_overlap_fails_closed:
  (source_execution bytecode_rejected_read_failure_guards_code
    corpus_read_failure_guards_unit corpus_read_failure_guards_program 1000
    ^(rejected_case "encoder_earlier_valid_overlap") =
   (Diagnostic InvalidCompletion, NONE, [])) ∧
  source_failure_reason bytecode_rejected_read_failure_guards_code
    corpus_read_failure_guards_unit corpus_read_failure_guards_program 1000
    ^(rejected_case "encoder_earlier_valid_overlap") = SOME "unsupported: encoder input at or above the free memory pointer"
Proof
  CONV_TAC cv_eval
QED

Theorem packed_earlier_valid_overlap_fails_closed:
  (source_execution bytecode_rejected_read_failure_guards_code
    corpus_read_failure_guards_unit corpus_read_failure_guards_program 1000
    ^(rejected_case "packed_earlier_valid_overlap") =
   (Diagnostic InvalidCompletion, NONE, [])) ∧
  source_failure_reason bytecode_rejected_read_failure_guards_code
    corpus_read_failure_guards_unit corpus_read_failure_guards_program 1000
    ^(rejected_case "packed_earlier_valid_overlap") = SOME "unsupported: encoder input at or above the free memory pointer"
Proof
  CONV_TAC cv_eval
QED

Theorem revert_overlap_fails_closed:
  (source_execution bytecode_rejected_read_failure_guards_code
    corpus_read_failure_guards_unit corpus_read_failure_guards_program 1000
    ^(rejected_case "revert_overlap") =
   (Diagnostic InvalidCompletion, NONE, [])) ∧
  source_failure_reason bytecode_rejected_read_failure_guards_code
    corpus_read_failure_guards_unit corpus_read_failure_guards_program 1000
    ^(rejected_case "revert_overlap") = SOME "unsupported: encoder input at or above the free memory pointer"
Proof
  CONV_TAC cv_eval
QED

Theorem emit_pointer_move_fails_closed:
  (source_execution bytecode_rejected_read_failure_guards_code
    corpus_read_failure_guards_unit corpus_read_failure_guards_program 1000
    ^(rejected_case "emit_pointer_move") =
   (Diagnostic InvalidCompletion, NONE, [])) ∧
  source_failure_reason bytecode_rejected_read_failure_guards_code
    corpus_read_failure_guards_unit corpus_read_failure_guards_program 1000
    ^(rejected_case "emit_pointer_move") = SOME "unsupported: encoder reach overlaps a free memory pointer moved by an event's hash preimage"
Proof
  CONV_TAC cv_eval
QED

(* No argument is read from memory, but the moved pointer puts the log's data
 * in scratch, where hashing the stored array's slot overwrites its offset. *)
Theorem emit_stored_pointer_move_fails_closed:
  (source_execution bytecode_rejected_read_failure_guards_code
    corpus_read_failure_guards_unit corpus_read_failure_guards_program 1000
    ^(rejected_case "emit_stored_pointer_move") =
   (Diagnostic InvalidCompletion, NONE, [])) ∧
  source_failure_reason bytecode_rejected_read_failure_guards_code
    corpus_read_failure_guards_unit corpus_read_failure_guards_program 1000
    ^(rejected_case "emit_stored_pointer_move") = SOME "unsupported: encoder reach overlaps a free memory pointer moved by an event's hash preimage"
Proof
  CONV_TAC cv_eval
QED
