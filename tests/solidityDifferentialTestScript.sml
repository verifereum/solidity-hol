(* The comparison itself: deliberately altered expectations and a mismatching
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
    corpus_pure_core_program 1000 "add" [IntArg 2; IntArg 3] []
    (ExpectReturn [IntArg 6]) [] =
  Unexpected (returned [Uint 8] [NumV 5]) (returned [Uint 8] [NumV 6])
Proof
  simp_tac std_ss [differential_verdict_def, LET_THM] >>
  CONV_TAC (cv_eval_call "observed_slots") >>
  CONV_TAC cv_eval
QED

Theorem altered_panic_code_detected:
  differential_verdict corpus_pure_core_code corpus_pure_core_unit
    corpus_pure_core_program 1000 "add" [IntArg 200; IntArg 100] []
    (ExpectPanic 0x12) [] =
  Unexpected (Reverted (panic_data 0x11)) (Reverted (panic_data 0x12))
Proof
  simp_tac std_ss [differential_verdict_def, LET_THM] >>
  CONV_TAC (cv_eval_call "observed_slots") >>
  CONV_TAC cv_eval
QED

Theorem altered_final_storage_detected:
  differential_verdict corpus_storage_code corpus_storage_unit
    corpus_storage_program 1000 "setTotal" [IntArg 7] []
    (ExpectReturn []) [(0, 8)] =
  StorageUnexpected [(1, 0); (2, 0); (3, 0); (0, 7)]
    [(1, 0); (2, 0); (3, 0); (0, 8)]
Proof
  simp_tac std_ss [differential_verdict_def, LET_THM] >>
  CONV_TAC (cv_eval_call "observed_slots") >>
  CONV_TAC cv_eval
QED

Theorem mismatching_fixture_detected:
  differential_verdict mutant_code corpus_pure_core_unit
    corpus_pure_core_program 1000 "add" [IntArg 200; IntArg 100] []
    (ExpectPanic 0x11) [] =
  Mismatch (returned [Uint 8] [NumV 44]) (Reverted (panic_data 0x11))
Proof
  simp_tac std_ss [differential_verdict_def, LET_THM] >>
  CONV_TAC (cv_eval_call "observed_slots") >>
  CONV_TAC cv_eval
QED

(* The mutant agrees where it behaves like the source. *)
Theorem mismatching_fixture_agrees_in_range:
  differential_agrees mutant_code corpus_pure_core_unit
    corpus_pure_core_program 1000 "add" [IntArg 2; IntArg 3] []
    (ExpectReturn [IntArg 5]) []
Proof
  simp_tac std_ss [differential_agrees_def, differential_verdict_def, LET_THM] >>
  CONV_TAC (cv_eval_call "observed_slots") >>
  CONV_TAC cv_eval
QED

Theorem fuel_exhaustion_inconclusive:
  differential_verdict corpus_pure_core_code corpus_pure_core_unit
    corpus_pure_core_program 1 "fact" [IntArg 5] []
    (ExpectReturn [IntArg 120]) [] =
  Inconclusive (returned [Uint 256] [NumV 120]) (Diagnostic OutOfFuel)
Proof
  simp_tac std_ss [differential_verdict_def, LET_THM] >>
  CONV_TAC (cv_eval_call "observed_slots") >>
  CONV_TAC cv_eval
QED

(* Equal diagnostics on both sides are still not agreement. *)
Theorem unknown_function_inconclusive:
  differential_verdict corpus_pure_core_code corpus_pure_core_unit
    corpus_pure_core_program 1000 "missing" [] [] (ExpectReturn []) [] =
  Inconclusive (Diagnostic UnknownFunction) (Diagnostic UnknownFunction)
Proof
  simp_tac std_ss [differential_verdict_def, LET_THM] >>
  CONV_TAC (cv_eval_call "observed_slots") >>
  CONV_TAC cv_eval
QED

Theorem argument_out_of_range_inconclusive:
  differential_verdict corpus_pure_core_code corpus_pure_core_unit
    corpus_pure_core_program 1000 "add" [IntArg 256; IntArg 0] []
    (ExpectReturn [IntArg 0]) [] =
  Inconclusive (Diagnostic UnencodableArguments)
    (Diagnostic UnencodableArguments)
Proof
  simp_tac std_ss [differential_verdict_def, LET_THM] >>
  CONV_TAC (cv_eval_call "observed_slots") >>
  CONV_TAC cv_eval
QED

(* The source-only mutant writes an unlisted mapping key. Both runs return zero
 * and agree on every old observed slot; their complete storage differs.
 *)
val unlisted_write = rhs (concl (EVAL
  “corpus_mappings_program with procedures :=
    MAP (λproc. if proc.procedure_id = AstId 41 then
      proc with body :=
        [DefineStmt (AstId 900000) (ReferenceType (MappingT (UintT 256) (UintT 8)))
           (StateReferenceOperation (AstId 5));
         DefineStmt (AstId 900001) (ReferenceType (UintT 8))
           (NavigateOperation (UintT 8) (BoundAtom (AstId 900000))
             (IndexNavigation (ConstantAtom (IntegerValue 987654321))));
         CaptureValueStmt (AstId 900002) (BoundAtom (AstId 900001));
         WriteScalarStmt (AstId 900002) (UintT 8)
           (ConstantAtom (IntegerValue 17))] ++ proc.body
      else proc) corpus_mappings_program.procedures”));

Definition unlisted_write_program_def:
  unlisted_write_program = ^unlisted_write
End

val () = cv_auto_trans unlisted_write_program_def;

Theorem unlisted_write_program_wf:
  wf_core_program (core_program_environment unlisted_write_program) unlisted_write_program
Proof
  CONV_TAC cv_eval
QED

Theorem unlisted_mapping_write_escaped_slot_projection:
  evm_observation corpus_mappings_code corpus_mappings_unit "read" [IntArg 0]
      [] (observed_slots unlisted_write_program [] []) =
  source_observation corpus_mappings_code corpus_mappings_unit
      unlisted_write_program 1000 "read" [IntArg 0] []
      (observed_slots unlisted_write_program [] [])
Proof
  CONV_TAC (cv_eval_call "observed_slots") >>
  CONV_TAC (cv_eval_call "evm_observation") >>
  CONV_TAC (cv_eval_call "source_observation") >> REFL_TAC
QED

Theorem unlisted_mapping_write_detected:
  differential_verdict corpus_mappings_code corpus_mappings_unit
    unlisted_write_program 1000 "read" [IntArg 0] []
    (ExpectReturn [IntArg 0]) [] =
  StorageMismatch [(0,0); (1,0); (2,0); (3,0); (4,0); (5,0); (6,0)]
                  [(0,0); (1,0); (2,0); (3,0); (4,0); (5,0); (6,0)]
Proof
  simp_tac std_ss [differential_verdict_def, LET_THM] >>
  CONV_TAC (cv_eval_call "observed_slots") >>
  CONV_TAC cv_eval
QED
