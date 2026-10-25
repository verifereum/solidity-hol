(* The comparison itself: a deliberately altered expectation and a mismatching
 * fixture are detected, and diagnostics are never agreement. The corpus
 * witnesses are in solidityDifferentialCorpus.
 *)
Theory solidityDifferentialTest
Ancestors
  solidityDifferential solidityDifferentialCorpus
Libs
  solidityImportLib cv_transLib wordsLib intLib

(* Read by holbuild's dependency scanner, which stages the fixture. *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../testdata/differential/expected/mutant.json"]

(* testdata/differential/mutant.sol: PureCore.add, but wrapping. *)
Definition mutant_code_def:
  mutant_code = REVERSE $ hex_to_rev_bytes [] $
    ^(stringSyntax.fromMLstring
        (artifact_deployed_bytecode
           "../testdata/differential/expected/mutant.json"
           "testdata/differential/mutant.sol" "Mutant"))
End

val () = cv_trans_deep_embedding EVAL mutant_code_def;

(* Evaluates the one call of the named function, so that the bytecode run,
 * the evaluator run and the comparison are separate proof steps.
 *)
fun cv_eval_call name =
  ONCE_DEPTH_CONV (fn t =>
    let val (f, _) = strip_comb t in
      if is_const f andalso fst (dest_const f) = name then cv_eval t
      else NO_CONV t
    end)

Theorem altered_expectation_detected:
  differential_verdict corpus_pure_core_code corpus_pure_core_unit
    corpus_pure_core_program 1000 "add" [IntArg 2; IntArg 3]
    (ExpectReturn [IntArg 6]) =
  Unexpected (returned [Uint 8] [NumV 5]) (returned [Uint 8] [NumV 6])
Proof
  rewrite_tac [differential_verdict_def] >>
  CONV_TAC (cv_eval_call "evm_outcome") >>
  CONV_TAC (cv_eval_call "source_outcome") >>
  CONV_TAC cv_eval
QED

Theorem altered_panic_code_detected:
  differential_verdict corpus_pure_core_code corpus_pure_core_unit
    corpus_pure_core_program 1000 "add" [IntArg 200; IntArg 100]
    (ExpectPanic 0x12) =
  Unexpected (Reverted (panic_data 0x11)) (Reverted (panic_data 0x12))
Proof
  rewrite_tac [differential_verdict_def] >>
  CONV_TAC (cv_eval_call "evm_outcome") >>
  CONV_TAC (cv_eval_call "source_outcome") >>
  CONV_TAC cv_eval
QED

Theorem mismatching_fixture_detected:
  differential_verdict mutant_code corpus_pure_core_unit
    corpus_pure_core_program 1000 "add" [IntArg 200; IntArg 100]
    (ExpectPanic 0x11) =
  Mismatch (returned [Uint 8] [NumV 44]) (Reverted (panic_data 0x11))
Proof
  rewrite_tac [differential_verdict_def] >>
  CONV_TAC (cv_eval_call "evm_outcome") >>
  CONV_TAC (cv_eval_call "source_outcome") >>
  CONV_TAC cv_eval
QED

(* The mutant agrees where it behaves like the source. *)
Theorem mismatching_fixture_agrees_in_range:
  differential_agrees mutant_code corpus_pure_core_unit
    corpus_pure_core_program 1000 "add" [IntArg 2; IntArg 3]
    (ExpectReturn [IntArg 5])
Proof
  rewrite_tac [differential_agrees_def, differential_verdict_def] >>
  CONV_TAC (cv_eval_call "evm_outcome") >>
  CONV_TAC (cv_eval_call "source_outcome") >>
  CONV_TAC cv_eval
QED

Theorem fuel_exhaustion_inconclusive:
  differential_verdict corpus_pure_core_code corpus_pure_core_unit
    corpus_pure_core_program 1 "fact" [IntArg 5] (ExpectReturn [IntArg 120]) =
  Inconclusive (returned [Uint 256] [NumV 120]) (Diagnostic OutOfFuel)
Proof
  rewrite_tac [differential_verdict_def] >>
  CONV_TAC (cv_eval_call "evm_outcome") >>
  CONV_TAC (cv_eval_call "source_outcome") >>
  CONV_TAC cv_eval
QED

(* Equal diagnostics on both sides are still not agreement. *)
Theorem unknown_function_inconclusive:
  differential_verdict corpus_pure_core_code corpus_pure_core_unit
    corpus_pure_core_program 1000 "missing" [] (ExpectReturn []) =
  Inconclusive (Diagnostic UnknownFunction) (Diagnostic UnknownFunction)
Proof
  rewrite_tac [differential_verdict_def] >>
  CONV_TAC (cv_eval_call "evm_outcome") >>
  CONV_TAC (cv_eval_call "source_outcome") >>
  CONV_TAC cv_eval
QED

Theorem argument_out_of_range_inconclusive:
  differential_verdict corpus_pure_core_code corpus_pure_core_unit
    corpus_pure_core_program 1000 "add" [IntArg 256; IntArg 0]
    (ExpectReturn [IntArg 0]) =
  Inconclusive (Diagnostic UnencodableArguments)
    (Diagnostic UnencodableArguments)
Proof
  rewrite_tac [differential_verdict_def] >>
  CONV_TAC (cv_eval_call "evm_outcome") >>
  CONV_TAC (cv_eval_call "source_outcome") >>
  CONV_TAC cv_eval
QED
