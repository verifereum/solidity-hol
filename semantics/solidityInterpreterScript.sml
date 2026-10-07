(* First executable ordered-core interpreter. External context, storage layouts,
 * navigation/allocation/copying are deliberately not guessed here.
 *)
Theory solidityInterpreter
Ancestors
  solidityValue solidityState solidityCore list arithmetic finite_map
Libs
  cv_transLib BasicProvers

Datatype:
  core_task
  = RunBlock (core_stmt list)
  | RunScopedBlock (core_stmt list)
  | RunStatement core_stmt
  | RunOperation core_operation
  | RunProcedure ast_id (runtime_value list)
  | RunWhile (core_stmt list) core_atom (core_stmt list)
End

Definition task_size_def:
  task_size (RunBlock statements) = 4 * list_size core_stmt_size statements + 2 ∧
  task_size (RunScopedBlock statements) = 4 * list_size core_stmt_size statements + 3 ∧
  task_size (RunStatement statement) = 4 * core_stmt_size statement + 1 ∧
  task_size (RunOperation operation) = 4 * core_operation_size operation ∧
  task_size (RunProcedure id values) = 0 ∧
  task_size (RunWhile prelude condition body) =
    4 * (list_size core_stmt_size prelude + core_atom_size condition +
         list_size core_stmt_size body) + 4
End

Definition source_outcome_def:
  source_outcome completion state evidence = <|
    completion := completion; state := state; unused_gas_evidence := evidence |>
End

Definition invalid_outcome_def:
  invalid_outcome message state evidence =
    source_outcome (InvalidCompletion message) state evidence
End

Definition initialise_parameters_def:
  initialise_parameters [] [] state = SOME state ∧
  initialise_parameters ((id,ty)::parameters) (value::values) state =
    (case define_binding id (SingleType ty) value state of
       NONE => NONE
     | SOME next => initialise_parameters parameters values next) ∧
  initialise_parameters _ _ state = NONE
End

Definition initialise_returns_def:
  initialise_returns [] state = SOME state ∧
  initialise_returns ((id,ty)::returns) state =
    (case default_scalar ty of
       NONE => NONE
     | SOME scalar =>
         case define_binding id (SingleType ty) (ScalarValue scalar) state of
           NONE => NONE
         | SOME next => initialise_returns returns next)
End

Definition close_scope_def:
  close_scope targets result =
    case result.state.scopes of
      [] => result with completion := InvalidCompletion "missing lexical scope"
    | scope::scopes => result with state :=
        result.state with <| scopes := scopes; targets := targets |>
End

Definition finish_invocation_def:
  finish_invocation procedure caller result =
    let values = case result.completion of
      NormalCompletion => eval_atoms (MAP (BoundAtom o FST) procedure.return_bindings) result.state
    | ReturnCompletion [] => eval_atoms (MAP (BoundAtom o FST) procedure.return_bindings) result.state
    | ReturnCompletion values => SOME values
    | _ => NONE in
    let completion = case result.completion of
      NormalCompletion =>
        (case values of SOME vs =>
           if values_match (MAP (SingleType o SND) procedure.return_bindings) vs
           then ReturnCompletion vs else InvalidCompletion "return type mismatch"
         | NONE => InvalidCompletion "missing return binding")
    | ReturnCompletion ignored =>
        (case values of SOME vs =>
           if values_match (MAP (SingleType o SND) procedure.return_bindings) vs
           then ReturnCompletion vs else InvalidCompletion "return type mismatch"
         | NONE => InvalidCompletion "missing return binding")
    | BreakCompletion => InvalidCompletion "break escaped procedure"
    | ContinueCompletion => InvalidCompletion "continue escaped procedure"
    | other => other in
    result with <| completion := completion;
      state := result.state with <| scopes := caller.scopes; targets := caller.targets |> |>
End

Definition pure_operation_def:
  pure_operation operation state =
    case operation of
      ScalarOperation ty mode op atoms =>
        (case eval_atoms atoms state of
           NONE => INL (InvalidCompletion "missing scalar operand")
         | SOME values => eval_scalar_operation ty mode op values)
    | ConvertOperation ty atom =>
        (case eval_atom atom state of
           SOME (ScalarValue (IntegerValue i)) => scalar_result ty UncheckedArithmetic i
         | SOME (ScalarValue scalar) =>
             if scalar_matches ty scalar then INR (ScalarValue scalar)
             else INL (InvalidCompletion "unsupported conversion")
         | _ => INL (InvalidCompletion "invalid conversion operand"))
    | TupleOperation atoms =>
        (case eval_atoms atoms state of
           NONE => INL (InvalidCompletion "missing tuple operand")
         | SOME values => INR (TupleValue values))
    | TupleComponentOperation index atom =>
        (case eval_atom atom state of
           SOME (TupleValue values) =>
             if index < LENGTH values then INR (EL index values)
             else INL (InvalidCompletion "tuple component out of bounds")
         | _ => INL (InvalidCompletion "tuple operand required"))
    | ReadOperation ty atom =>
        (case eval_atom atom state of
           SOME (ReferenceValue reference) =>
             (case read_memory ty reference state of
                SOME value => INR value
              | NONE => INL (InvalidCompletion "unsupported or invalid reference read"))
         | _ => INL (InvalidCompletion "reference operand required"))
    | _ => INL (InvalidCompletion "unsupported operation")
End

Definition procedures_named_def:
  procedures_named program id =
    FILTER (λprocedure. procedure.procedure_id = id) program.procedures
End

Definition eval_core_def:
  eval_core fuel program (RunBlock []) state evidence =
    source_outcome NormalCompletion state evidence ∧
  eval_core fuel program (RunBlock (statement::statements)) state evidence =
    (let result = eval_core fuel program (RunStatement statement) state evidence in
       if result.completion = NormalCompletion
       then eval_core fuel program (RunBlock statements) result.state result.unused_gas_evidence
       else result) ∧
  eval_core fuel program (RunScopedBlock statements) state evidence =
    close_scope state.targets
      (eval_core fuel program (RunBlock statements)
        (state with scopes := FEMPTY::state.scopes) evidence) ∧
  eval_core fuel program (RunStatement statement) state evidence =
    (case statement of
       DefineStmt id ty operation =>
         (let result = eval_core fuel program (RunOperation operation) state evidence in
          case result.completion of
            ReturnCompletion [value] =>
              (case define_binding id ty value result.state of
                 NONE => invalid_outcome "invalid definition" result.state result.unused_gas_evidence
               | SOME next => source_outcome NormalCompletion next result.unused_gas_evidence)
          | _ => result)
     | CaptureBindingStmt target id =>
         (case lookup_binding id state.scopes of
            NONE => invalid_outcome "missing captured binding" state evidence
          | SOME binding => source_outcome NormalCompletion
              (state with targets := state.targets |+ (ast_key target, BindTarget id)) evidence)
     | CaptureValueStmt target atom =>
         (case eval_atom atom state of
            SOME (ReferenceValue reference) => source_outcome NormalCompletion
              (state with targets := state.targets |+ (ast_key target, ValueTarget reference)) evidence
          | _ => invalid_outcome "reference capture required" state evidence)
     | WriteScalarStmt target ty atom =>
         (case (FLOOKUP state.targets (ast_key target), eval_atom atom state) of
            (SOME captured, SOME value) =>
              (case write_target F captured ty value state of
                 NONE => invalid_outcome "invalid scalar write" state evidence
               | SOME next => source_outcome NormalCompletion next evidence)
          | _ => invalid_outcome "missing write target or value" state evidence)
     | BindReferenceStmt target ty atom =>
         (case (FLOOKUP state.targets (ast_key target), eval_atom atom state) of
            (SOME captured, SOME value) =>
              (case write_target T captured ty value state of
                 NONE => invalid_outcome "invalid reference binding" state evidence
               | SOME next => source_outcome NormalCompletion next evidence)
          | _ => invalid_outcome "missing binding target or value" state evidence)
     | IfStmt condition yes no =>
         (case eval_atom condition state of
            SOME (ScalarValue (BoolValue b)) =>
              eval_core fuel program (RunScopedBlock (if b then yes else no)) state evidence
          | _ => invalid_outcome "boolean condition required" state evidence)
     | WhileStmt prelude condition body =>
         eval_core fuel program (RunWhile prelude condition body) state evidence
     | ReturnStmt atoms =>
         (case eval_atoms atoms state of
            NONE => invalid_outcome "missing return operand" state evidence
          | SOME values => source_outcome (ReturnCompletion values) state evidence)
     | BreakStmt => source_outcome BreakCompletion state evidence
     | ContinueStmt => source_outcome ContinueCompletion state evidence
     | RevertStmt atom =>
         (case eval_atom atom state of
            SOME (ScalarValue (BytesValue bytes)) => source_outcome (RevertCompletion bytes) state evidence
          | _ => invalid_outcome "revert bytes required" state evidence)
     | _ => invalid_outcome "unsupported statement" state evidence) ∧
  eval_core fuel program (RunOperation operation) state evidence =
    (case operation of
       InternalCallOperation id atoms =>
         (case eval_atoms atoms state of
            NONE => invalid_outcome "missing call argument" state evidence
          | SOME values =>
              let result = eval_core fuel program (RunProcedure id values) state evidence in
              case result.completion of
                ReturnCompletion returns => result with completion := ReturnCompletion [TupleValue returns]
              | _ => result)
     | _ => (case pure_operation operation state of
         INL completion => source_outcome completion state evidence
       | INR value => source_outcome (ReturnCompletion [value]) state evidence)) ∧
  eval_core fuel program (RunProcedure id values) state evidence =
    (case procedures_named program id of
       [procedure] =>
         (case initialise_parameters procedure.parameters values
           (state with <| scopes := [FEMPTY]; targets := FEMPTY |>) of
            NONE => invalid_outcome "invalid procedure arguments" state evidence
          | SOME parameters =>
              case initialise_returns procedure.return_bindings parameters of
                NONE => invalid_outcome "unsupported or invalid return bindings" state evidence
              | SOME entered =>
                  case fuel of
                    0 => source_outcome FuelExhausted state evidence
                  | SUC remaining => finish_invocation procedure state
                      (eval_core remaining program (RunBlock procedure.body) entered evidence))
     | _ => invalid_outcome "missing or duplicate procedure" state evidence) ∧
  eval_core fuel program (RunWhile prelude condition body) state evidence =
    (let tested = eval_core fuel program (RunBlock prelude)
       (state with scopes := FEMPTY::state.scopes) evidence in
     if tested.completion ≠ NormalCompletion then close_scope state.targets tested else
     case eval_atom condition tested.state of
       SOME (ScalarValue (BoolValue b)) =>
         (if ¬b then close_scope state.targets tested else
          let executed = eval_core fuel program (RunScopedBlock body)
            tested.state tested.unused_gas_evidence in
          let closed = close_scope state.targets executed in
          if closed.completion = NormalCompletion ∨ closed.completion = ContinueCompletion
          then (case fuel of
                  0 => closed with completion := FuelExhausted
                | SUC remaining => eval_core remaining program
                    (RunWhile prelude condition body) closed.state closed.unused_gas_evidence)
          else if closed.completion = BreakCompletion
          then closed with completion := NormalCompletion
          else closed)
     | _ => close_scope state.targets
         (invalid_outcome "boolean loop condition required" tested.state tested.unused_gas_evidence))
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λ(fuel,program,task,state,evidence). (fuel,task_size task))’
  \\ simp[task_size_def]
  \\ rpt strip_tac
  \\ Cases_on ‘b’
  \\ simp[]
End

val () = List.app cv_auto_trans
  [source_outcome_def, invalid_outcome_def, initialise_parameters_def];

val initialise_returns_pre_def =
  cv_trans_pre "initialise_returns_pre" initialise_returns_def;

Theorem initialise_returns_pre[cv_pre]:
  ∀returns state. initialise_returns_pre returns state
Proof
  ho_match_mp_tac initialise_returns_ind
  \\ rpt strip_tac
  \\ ONCE_REWRITE_TAC [initialise_returns_pre_def]
  \\ rw[]
  \\ fs[]
QED

val () = List.app cv_auto_trans
  [close_scope_def, finish_invocation_def, pure_operation_def, procedures_named_def,
   recordtype_source_result_seldef_unused_gas_evidence_def,
   recordtype_core_procedure_seldef_parameters_def,
   recordtype_core_procedure_seldef_body_def];

(* Destruct only CV fields relevant to the termination measure. *)
fun split_cv_measure (asms, goal) =
  let
    val vars = free_vars goal
    fun wanted tm = is_comb tm andalso is_var (rand tm) andalso
      List.exists (aconv (rand tm)) vars andalso
      List.exists (aconv (rator tm)) [“cv_fst”, “cv_snd”]
    val projection = find_term wanted (first (can (find_term wanted)) (goal::asms))
  in
    Cases_on [ANTIQUOTE (rand projection)] (asms, goal)
  end;

Definition cv_task_rank_def:
  cv_task_rank task =
    if cv$c2n (cv_fst task) = 4 then 0 else
    4 * cv_size (cv_snd task) +
    if cv$c2n (cv_fst task) = 0 then 2 else
    if cv$c2n (cv_fst task) = 1 then 3 else
    if cv$c2n (cv_fst task) = 2 then 1 else
    if cv$c2n (cv_fst task) = 3 then 0 else 4
End

val eval_core_pre_def = cv_trans_pre_rec "eval_core_pre" eval_core_def
  (WF_REL_TAC ‘inv_image ($< LEX $<)
    (λ(fuel,program,task,state,evidence). (cv$c2n fuel, cv_task_rank task))’
   \\ rpt strip_tac
   \\ TRY (Cases_on ‘cv_fuel’)
   \\ TRY (Cases_on ‘cv_v’)
   \\ TRY (Cases_on ‘g’)
   \\ fs[cvTheory.cv_eq_def, cvTheory.cv_lt_def, cvTheory.c2b_def]
   \\ rw[cv_task_rank_def]
   \\ rpt (split_cv_measure \\ fs[cvTheory.cv_eq_def, cvTheory.cv_lt_def, cvTheory.c2b_def])
   \\ TRY (Cases_on ‘g’)
   \\ fs[cvTheory.cv_lt_def, cvTheory.cv_eq_def, cvTheory.c2b_def, AllCaseEqs()]
   \\ Cases_on ‘g''’
   \\ fs[cvTheory.cv_lt_def, cvTheory.c2b_def, AllCaseEqs()]);

Theorem eval_core_pre[cv_pre]:
  ∀fuel program task state evidence. eval_core_pre fuel program task state evidence
Proof
  ho_match_mp_tac eval_core_ind
  \\ rpt strip_tac
  \\ Cases_on ‘state’
  \\ ONCE_REWRITE_TAC [eval_core_pre_def]
  \\ rw[]
  \\ gvs[source_state_fn_updates, source_result_fn_updates]
QED

Definition eval_block_def:
  eval_block fuel program statements state evidence =
    eval_core fuel program (RunBlock statements) state evidence
End

Definition invoke_source_def:
  invoke_source fuel program id values state evidence =
    eval_core fuel program (RunProcedure id values) state evidence
End

val () = cv_auto_trans eval_block_def;
val () = cv_auto_trans invoke_source_def;

Definition run_source_def:
  run_source fuel program arguments state evidence =
    invoke_source fuel program program.entry_procedure arguments state evidence
End

val () = cv_auto_trans run_source_def;

Theorem pure_operation_fuel_independent:
  (∀id atoms. operation ≠ InternalCallOperation id atoms) ⇒
  eval_core fuel program (RunOperation operation) state evidence =
  eval_core other_fuel program (RunOperation operation) state evidence
Proof
  Cases_on ‘operation’
  \\ simp[eval_core_def]
QED

Theorem invocation_restores_caller_bindings_and_targets:
  (invoke_source fuel program id values state evidence).state.scopes = state.scopes ∧
  (invoke_source fuel program id values state evidence).state.targets = state.targets
Proof
  simp[invoke_source_def, eval_core_def]
  \\ every_case_tac
  \\ simp[source_outcome_def, invalid_outcome_def, finish_invocation_def]
QED
