(* Concrete-frame experiment: NOT yet the source-to-EVM adapter.
 * Input is an existing EVM caller positioned at the requested opcode, with
 * concrete stack/memory/gas/checkpoints already supplied. No state rebuilding.
 *)
Theory solidityEVMCall
Ancestors
  solidityState vfmCompute
Libs
  cv_transLib

Datatype:
  boundary_instruction
  = BoundaryCall
  | BoundaryStaticCall
  | BoundaryDelegateCall
  | BoundaryCreate
  | BoundaryCreate2
End

Definition boundary_opcode_def:
  boundary_opcode BoundaryCall = Call ∧
  boundary_opcode BoundaryStaticCall = StaticCall ∧
  boundary_opcode BoundaryDelegateCall = DelegateCall ∧
  boundary_opcode BoundaryCreate = Create ∧
  boundary_opcode BoundaryCreate2 = Create2
End

val () = cv_auto_trans boundary_opcode_def;

Definition positioned_at_boundary_def:
  positioned_at_boundary instruction (es : execution_state) ⇔
    case es.contexts of
      [] => F
    | (ctxt, checkpoint)::rest =>
        FLOOKUP ctxt.msgParams.parsed ctxt.pc = SOME (boundary_opcode instruction)
End

val () = cv_auto_trans positioned_at_boundary_def;

(* step includes handle_step: precompile completion/failure can happen DURING
 * entry. Only run a subtree if entry left a child frame on the stack.
 *)
Definition execute_boundary_def:
  execute_boundary instruction es =
    if ¬positioned_at_boundary instruction es then NONE else
    case step es of
      (INR e, next) => SOME (INR e, next)
    | (INL (), next) =>
        if LENGTH next.contexts > LENGTH es.contexts
        then run_call next
        else SOME (INL (), next)
End

val () = cv_auto_trans execute_boundary_def;

Datatype:
  boundary_outcome
  = BoundaryReturned bytes32 (byte list) execution_state
  | BoundaryAborted (exception option) execution_state
  | BoundaryCallerExited execution_state
  | BoundaryMalformed execution_state
  | BoundaryWrongPosition
  | BoundaryNoResult
End

(* For CALL-family opcodes the word is the low-level success flag; for CREATE
 * it is the created address or zero. A nested EVM revert/exception returns to
 * the caller normally with a zero word. Its precise halt reason is not exposed
 * by this low-level boundary; source ABI/try-catch classification uses bytes.
 *)
Definition observe_boundary_def:
  observe_boundary initial result =
    case result of
      NONE => BoundaryNoResult
    | SOME (INR e, final) => BoundaryAborted e final
    | SOME (INL (), final) =>
        if LENGTH final.contexts < LENGTH initial.contexts
        then BoundaryCallerExited final
        else if LENGTH final.contexts > LENGTH initial.contexts
        then BoundaryMalformed final
        else case final.contexts of
          [] => BoundaryMalformed final
        | (ctxt, checkpoint)::rest =>
            case ctxt.stack of
              [] => BoundaryMalformed final
            | word::stack => BoundaryReturned word ctxt.returnData final
End

val () = cv_auto_trans observe_boundary_def;

Definition invoke_boundary_def:
  invoke_boundary instruction es =
    if positioned_at_boundary instruction es
    then observe_boundary es (execute_boundary instruction es)
    else BoundaryWrongPosition
End

val () = cv_auto_trans invoke_boundary_def;

Theorem boundary_rejects_wrong_position:
  ¬positioned_at_boundary instruction es ⇒
  execute_boundary instruction es = NONE
Proof
  simp[execute_boundary_def]
QED

Theorem boundary_handles_entry_abort:
  positioned_at_boundary instruction es ∧ step es = (INR e, next) ⇒
  execute_boundary instruction es = SOME (INR e, next)
Proof
  simp[execute_boundary_def]
QED

Theorem boundary_does_not_run_caller_suffix:
  positioned_at_boundary instruction es ∧ step es = (INL (), next) ∧
  LENGTH next.contexts ≤ LENGTH es.contexts ⇒
  execute_boundary instruction es = SOME (INL (), next)
Proof
  simp[execute_boundary_def]
QED

(* Upstream already proves the unbounded gas-based driver returns SOME.
 * No additional source fuel, guessed wf premise, or termination axiom needed.
 *)
Theorem boundary_execution_has_result:
  positioned_at_boundary instruction es ⇒
  IS_SOME (execute_boundary instruction es)
Proof
  strip_tac
  \\ Cases_on ‘step es’
  \\ rename1 ‘(result, next)’
  \\ Cases_on ‘result’
  \\ simp[execute_boundary_def, vfmDecreasesGasTheory.run_call_eq_tr]
  \\ rw[]
QED
