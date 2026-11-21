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

Theorem encoder_overlap_return_fails_closed:
  source_execution bytecode_rejected_read_failure_guards_code
    corpus_read_failure_guards_unit corpus_read_failure_guards_program 1000
    ^(rejected_case "encoder_overlap_return") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem encoder_overlap_first_fails_closed:
  source_execution bytecode_rejected_read_failure_guards_code
    corpus_read_failure_guards_unit corpus_read_failure_guards_program 1000
    ^(rejected_case "encoder_overlap_first") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem encoder_earlier_valid_overlap_fails_closed:
  source_execution bytecode_rejected_read_failure_guards_code
    corpus_read_failure_guards_unit corpus_read_failure_guards_program 1000
    ^(rejected_case "encoder_earlier_valid_overlap") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem packed_earlier_valid_overlap_fails_closed:
  source_execution bytecode_rejected_read_failure_guards_code
    corpus_read_failure_guards_unit corpus_read_failure_guards_program 1000
    ^(rejected_case "packed_earlier_valid_overlap") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem revert_overlap_fails_closed:
  source_execution bytecode_rejected_read_failure_guards_code
    corpus_read_failure_guards_unit corpus_read_failure_guards_program 1000
    ^(rejected_case "revert_overlap") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem emit_pointer_move_fails_closed:
  source_execution bytecode_rejected_read_failure_guards_code
    corpus_read_failure_guards_unit corpus_read_failure_guards_program 1000
    ^(rejected_case "emit_pointer_move") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED

(* No argument is read from memory, but the moved pointer puts the log's data
 * in scratch, where hashing the stored array's slot overwrites its offset. *)
Theorem emit_stored_pointer_move_fails_closed:
  source_execution bytecode_rejected_read_failure_guards_code
    corpus_read_failure_guards_unit corpus_read_failure_guards_program 1000
    ^(rejected_case "emit_stored_pointer_move") =
  (Diagnostic InvalidCompletion, NONE, [])
Proof
  CONV_TAC cv_eval
QED
