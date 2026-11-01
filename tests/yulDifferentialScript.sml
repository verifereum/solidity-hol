(* Running the pinned compiler's own Yul on the differential corpus, and
 * comparing what it does with what the corpus already establishes.
 *
 * The corpus theory (solidityDifferentialCorpus) holds the elaborated core and
 * verifereum's EVM, on the compiled bytecode, to each case's committed
 * expectation: the outcome it declares and the storage it lists. This theory
 * holds the Yul semantics to the same expectation, on the Yul the same
 * compiler emitted for the same source, at the three stages the design
 * separates (docs/roadmap.md, milestone 2): irAst, the code generator's own
 * output; irOptimizedAst with the optimizer off, after the transformations
 * solc runs then; and irOptimizedAst with the optimizer on, which is what a
 * production build hands to the backend.
 *
 * A run is a frame, as at the EVM boundary: the contract account at
 * contract_address holding the case's initial storage, the case's calldata,
 * no call value, and nothing else. Its observation is the outcome the EVM
 * sees (a return of ABI-encoded data, a revert, or a diagnostic), the
 * contract's committed storage, and the log the frame wrote; a revert takes
 * the initial world back, as finish_yul_frame says. The calldata is built by
 * the same call_data the bytecode run uses, so the two sides are called
 * identically, and the verdict is solidityDifferential's own, with the Yul
 * run standing where the core run stands: a Mismatch is the bytecode run and
 * the Yul run disagreeing on the outcome, an Unexpected is both agreeing on
 * something the case does not declare, Inconclusive is either side being a
 * diagnostic, and the storage verdicts compare complete committed storage.
 *
 * The log is part of the agreement: the corpus's other two sides record none
 * (the core evaluator's frames have no log, and run_transaction does not
 * expose the EVM's), so a Yul run that writes one is not agreement, and the
 * case is reported for classification instead of passing silently.
 *)
Theory yulDifferential
Ancestors
  solidityDifferential yulAST yulState yulEvaluator
Libs
  cv_transLib wordsLib intLib

Definition yul_differential_machine_def:
  yul_differential_machine data storage =
    <| accounts := contract_accounts [] storage;
       logs := [];
       self_address := contract_address;
       call_value := 0w;
       call_data := data;
       memory := FEMPTY;
       memory_size := 0;
       scopes := [] |>
End

Datatype:
  yul_observation = <|
    observed_outcome : call_outcome;
    observed_storage : storage option;
    observed_logs : event list
  |>
End

(* What the frame's caller sees, as finish_yul_frame decides it. *)
Definition yul_frame_observation_def:
  yul_frame_observation frames =
    case frames of
      YulFrameSuccess data w =>
        <| observed_outcome := Returned data;
           observed_storage := SOME (lookup_account contract_address w.accounts).storage;
           observed_logs := w.logs |>
    | YulFrameRevert data w =>
        <| observed_outcome := Reverted data;
           observed_storage := SOME (lookup_account contract_address w.accounts).storage;
           observed_logs := w.logs |>
    | YulFrameInvalid _ =>
        <| observed_outcome := Diagnostic InvalidCompletion;
           observed_storage := NONE;
           observed_logs := [] |>
    | YulFrameResourceLimit =>
        <| observed_outcome := Diagnostic OutOfFuel;
           observed_storage := NONE;
           observed_logs := [] |>
End

Definition yul_execution_def:
  yul_execution code fuel data storage =
    let m = yul_differential_machine data storage in
    let r = run_yul fuel code m in
    yul_frame_observation (finish_yul_frame m r.machine r.completion)
End

(* A case's call: the same calldata the bytecode run is given, so an
 * unencodable argument or an unknown function is the same diagnostic on both
 * sides.
 *)
Definition yul_case_execution_def:
  yul_case_execution u name args storage code fuel =
    case function_types u name of
      NONE => <| observed_outcome := Diagnostic UnknownFunction;
                 observed_storage := NONE; observed_logs := [] |>
    | SOME (params, rets) =>
        case argument_values params args of
          NONE => <| observed_outcome := Diagnostic UnencodableArguments;
                     observed_storage := NONE; observed_logs := [] |>
        | SOME vs =>
            case call_data name params vs of
              NONE => <| observed_outcome := Diagnostic UnencodableArguments;
                         observed_storage := NONE; observed_logs := [] |>
            | SOME data => yul_execution code fuel data storage
End

(* The verdict on one case at one stage, with the log the run wrote. *)
Definition yul_case_verdict_def:
  yul_case_verdict code u prog name args storage e final yfuel ycode =
    let slots = observed_slots prog storage final in
    let evm_run = evm_execution code u name args storage in
    let run = yul_case_execution u name args storage ycode yfuel in
    let evm = project_observation slots evm_run in
    let yul = project_observation slots (run.observed_outcome, run.observed_storage) in
    (case compare_observations
            (expected_outcome u name e, expected_storage storage final slots)
            evm yul of
       Agree outcome =>
         if SND evm_run ≠ run.observed_storage then
           StorageMismatch (SND evm) (SND yul)
         else if SND evm_run ≠ SOME (seed_storage (final ++ storage)) then
           StorageUnexpected (SND evm) (expected_storage storage final slots)
         else Agree outcome
     | other => other,
     run.observed_logs)
End

Definition yul_agrees_def:
  yul_agrees code u prog name args storage e final yfuel ycode ⇔
    is_agreement (FST (yul_case_verdict code u prog name args storage e final yfuel ycode)) ∧
    SND (yul_case_verdict code u prog name args storage e final yfuel ycode) = []
End

(* What an agreement establishes: the Yul run returns or reverts what the case
 * expects, at the complete storage it expects, and leaves no log.
 *)
Theorem yul_agrees_outcomes:
  yul_agrees code u prog name args storage e final yfuel ycode ∧
  slots = observed_slots prog storage final ⇒
  ¬is_diagnostic (FST (yul_case_verdict code u prog name args storage e final yfuel ycode)) ∧
  FST (yul_case_verdict code u prog name args storage e final yfuel ycode) =
    Agree (expected_outcome u name e) ∧
  (yul_case_execution u name args storage ycode yfuel).observed_outcome =
    expected_outcome u name e ∧
  (yul_case_execution u name args storage ycode yfuel).observed_storage =
    SOME (seed_storage (final ++ storage)) ∧
  (yul_case_execution u name args storage ycode yfuel).observed_logs = []
Proof
  rw[yul_agrees_def, yul_case_verdict_def, is_agreement_def, is_diagnostic_def] >>
  BasicProvers.every_case_tac >> gvs[is_agreement_def]
QED

val () = cv_auto_trans yul_differential_machine_def;
val () = cv_auto_trans yul_frame_observation_def;
val () = cv_auto_trans yul_execution_def;
val () = cv_auto_trans yul_case_execution_def;
val () = cv_auto_trans yul_case_verdict_def;
val () = cv_auto_trans yul_agrees_def;
