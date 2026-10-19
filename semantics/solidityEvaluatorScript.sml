(* Pure evaluator: locals, control flow and internal calls over the stage-2
 * core, fuel-indexed by recursive depth.
 *
 * Fuel: statement-list traversal is structural and siblings reuse the bound;
 * invoke_source decrements on entry and a while loop decrements on its back
 * edge, so straight-line code and a loop's first iteration need none. No step
 * counter is threaded through the state.
 *
 * Scopes: an if branch and each loop iteration run in a pushed scope, and
 * leaving pops only that scope, so writes to enclosing bindings survive. A
 * procedure runs in a fresh scope and target map; the caller's are restored
 * afterwards, since the pure fragment has no references through which a callee
 * could reach them. Within a procedure, capturing a target overwrites it.
 *
 * Gas evidence is passed through unchanged; the EVM boundary is out of scope.
 * Unsupported statements and operations, and anything the checker would reject,
 * end in InvalidCompletion.
 *)
Theory solidityEvaluator
Ancestors
  solidityState solidityScalar vfmCompute
Libs
  cv_transLib wordsLib intLib

(* Scopes and targets *)

Definition lookup_binding_def:
  (lookup_binding x [] = NONE) ∧
  (lookup_binding x (scope :: scopes) =
    case ALOOKUP scope x of
      SOME b => SOME b
    | NONE => lookup_binding x scopes)
End

Definition set_binding_value_def:
  (set_binding_value x v [] = []) ∧
  (set_binding_value x v ((y, b) :: rest) =
    if x = y then (y, b with binding_value := v) :: rest
    else (y, b) :: set_binding_value x v rest)
End

(* Writes the binding in the innermost scope that holds it. *)
Definition update_binding_def:
  (update_binding x v [] = NONE) ∧
  (update_binding x v (scope :: scopes) =
    case ALOOKUP scope x of
      SOME _ => SOME (set_binding_value x v scope :: scopes)
    | NONE =>
        (case update_binding x v scopes of
           SOME scopes' => SOME (scope :: scopes')
         | NONE => NONE))
End

Definition bind_local_def:
  (bind_local x b [] = [[(x, b)]]) ∧
  (bind_local x b (scope :: scopes) = ((x, b) :: scope) :: scopes)
End

Definition delete_key_def:
  (delete_key k [] = []) ∧
  (delete_key k ((k', v) :: rest) =
    if k = k' then delete_key k rest else (k', v) :: delete_key k rest)
End

Definition set_target_def:
  set_target t target targets = (t, target) :: delete_key t targets
End

Definition push_scope_def:
  push_scope (st : source_state) = st with scopes := [] :: st.scopes
End

Definition pop_scopes_def:
  (pop_scopes [] = []) ∧
  (pop_scopes (_ :: scopes) = scopes)
End

(* Results *)

Definition normal_result_def:
  normal_result st gas =
    <| completion := NormalCompletion; state := st;
       unused_gas_evidence := gas |>
End

Definition abrupt_result_def:
  abrupt_result c st gas =
    <| completion := c; state := st; unused_gas_evidence := gas |>
End

Definition pop_result_def:
  pop_result (r : source_result) =
    r with state := (r.state with scopes := pop_scopes r.state.scopes)
End

(* Atoms and pure operations *)

Definition eval_atom_def:
  (eval_atom scopes (ConstantAtom s) = SOME (ScalarValue s)) ∧
  (eval_atom scopes (BoundAtom x) =
    case lookup_binding x scopes of
      SOME b => SOME b.binding_value
    | NONE => NONE)
End

Definition eval_atoms_def:
  (eval_atoms scopes [] = SOME []) ∧
  (eval_atoms scopes (a :: atoms) =
    case (eval_atom scopes a, eval_atoms scopes atoms) of
      (SOME v, SOME vs) => SOME (v :: vs)
    | _ => NONE)
End

Definition scalar_values_def:
  (scalar_values [] = SOME []) ∧
  (scalar_values (ScalarValue s :: vs) =
    case scalar_values vs of SOME ss => SOME (s :: ss) | NONE => NONE) ∧
  (scalar_values (_ :: _) = NONE)
End

Definition nth_value_def:
  (nth_value (n : num) [] = NONE) ∧
  (nth_value n (v :: vs) = if n = 0 then SOME v else nth_value (n - 1) vs)
End

(* The source type of a conversion: a binding's declared type, or the target
 * type for a constant (the literal/default-initialisation form).
 *)
Definition conversion_source_type_def:
  (conversion_source_type scopes ty (ConstantAtom _) = SOME ty) ∧
  (conversion_source_type scopes ty (BoundAtom x) =
    case lookup_binding x scopes of
      SOME b =>
        (case b.binding_type of SingleType src => SOME src | _ => NONE)
    | NONE => NONE)
End

Datatype:
  value_outcome = ValueOk runtime_value | ValueAbrupt source_completion
End

Definition scalar_outcome_value_def:
  scalar_outcome_value (ScalarOk s) = ValueOk (ScalarValue s) ∧
  scalar_outcome_value (ScalarPanic code) = ValueAbrupt (PanicCompletion code) ∧
  scalar_outcome_value ScalarInvalid =
    ValueAbrupt (InvalidCompletion "ill-typed scalar operands")
End

(* Every operation except an internal call, which needs the evaluator. *)
Definition eval_pure_operation_def:
  eval_pure_operation env scopes op =
    case op of
      ScalarOperation ty mode oper atoms =>
        (case eval_atoms scopes atoms of
           NONE => ValueAbrupt (InvalidCompletion "unbound atom")
         | SOME vs =>
             (case scalar_values vs of
                NONE => ValueAbrupt (InvalidCompletion "non-scalar operand")
              | SOME ss =>
                  scalar_outcome_value
                    (eval_scalar_operation env ty mode oper ss)))
    | ConvertOperation ty a =>
        (case (conversion_source_type scopes ty a, eval_atom scopes a) of
           (SOME src, SOME (ScalarValue s)) =>
             scalar_outcome_value (eval_conversion env src ty s)
         | _ => ValueAbrupt (InvalidCompletion "ill-typed conversion"))
    | TupleOperation atoms =>
        (case eval_atoms scopes atoms of
           SOME vs => ValueOk (TupleValue vs)
         | NONE => ValueAbrupt (InvalidCompletion "unbound atom"))
    | TupleComponentOperation n a =>
        (case eval_atom scopes a of
           SOME (TupleValue vs) =>
             (case nth_value n vs of
                SOME v => ValueOk v
              | NONE => ValueAbrupt (InvalidCompletion "tuple index"))
         | _ => ValueAbrupt (InvalidCompletion "not a tuple"))
    | _ => ValueAbrupt (InvalidCompletion "unsupported operation")
End

(* Procedures *)

Definition default_elementary_def:
  default_elementary ty =
    case ty of
      BoolT => SOME (BoolValue F)
    | UintT _ => SOME (IntegerValue 0)
    | IntT _ => SOME (IntegerValue 0)
    | AddressT _ => SOME (AddressValue 0w)
    | FixedBytesT n => SOME (BytesValue (REPLICATE n 0w))
    | _ => NONE
End

Definition default_scalar_def:
  default_scalar env ty =
    case ty of
      EnumT _ => SOME (IntegerValue 0)
    | UserValueT id =>
        (case lookup_user_value env id of
           SOME u => default_elementary u
         | NONE => NONE)
    | _ => default_elementary ty
End

Definition single_binding_def:
  single_binding ty v = <| binding_type := SingleType ty; binding_value := v |>
End

Definition bind_parameters_def:
  (bind_parameters [] [] = SOME []) ∧
  (bind_parameters ((x, ty) :: params) (v :: vs) =
    case bind_parameters params vs of
      SOME scope => SOME ((x, single_binding ty v) :: scope)
    | NONE => NONE) ∧
  (bind_parameters _ _ = NONE)
End

Definition bind_defaults_def:
  (bind_defaults env [] = SOME []) ∧
  (bind_defaults env ((x, ty) :: rets) =
    case (default_scalar env ty, bind_defaults env rets) of
      (SOME s, SOME scope) =>
        SOME ((x, single_binding ty (ScalarValue s)) :: scope)
    | _ => NONE)
End

(* Parameters bound to arguments, return bindings default-initialised. *)
Definition entry_scope_def:
  entry_scope env (p : core_procedure) args =
    case (bind_parameters p.parameters args, bind_defaults env p.return_bindings)
    of
      (SOME params, SOME rets) => SOME (params ++ rets)
    | _ => NONE
End

Definition read_returns_def:
  (read_returns scopes [] = SOME []) ∧
  (read_returns scopes ((x, _) :: rets) =
    case (lookup_binding x scopes, read_returns scopes rets) of
      (SOME b, SOME vs) => SOME (b.binding_value :: vs)
    | _ => NONE)
End

(* A call's value, following call_result_type: nothing, one value, or a tuple. *)
Definition pack_results_def:
  (pack_results [] = TupleValue []) ∧
  (pack_results [v] = v) ∧
  (pack_results vs = TupleValue vs)
End

(* The evaluator *)

Definition eval_block_def:
  (eval_block (n : num) env [] st gas = normal_result st gas) ∧
  (eval_block n env (DefineStmt x ty (InternalCallOperation f atoms) :: ss)
     st gas =
    case eval_atoms st.scopes atoms of
      NONE => abrupt_result (InvalidCompletion "unbound atom") st gas
    | SOME args =>
        let r = invoke_source n env f args st gas in
        case r.completion of
          ReturnCompletion vs =>
            eval_block n env ss
              (r.state with scopes :=
                 bind_local x <| binding_type := ty;
                                 binding_value := pack_results vs |>
                   r.state.scopes)
              r.unused_gas_evidence
        | _ => r) ∧
  (eval_block n env (DefineStmt x ty op :: ss) st gas =
    case eval_pure_operation env st.scopes op of
      ValueOk v =>
        eval_block n env ss
          (st with scopes :=
             bind_local x <| binding_type := ty; binding_value := v |>
               st.scopes)
          gas
    | ValueAbrupt c => abrupt_result c st gas) ∧
  (eval_block n env (CaptureBindingStmt t x :: ss) st gas =
    eval_block n env ss
      (st with targets := set_target t (BindTarget x) st.targets) gas) ∧
  (eval_block n env (WriteScalarStmt t ty a :: ss) st gas =
    case (ALOOKUP st.targets t, eval_atom st.scopes a) of
      (SOME (BindTarget x), SOME v) =>
        (case update_binding x v st.scopes of
           SOME scopes => eval_block n env ss (st with scopes := scopes) gas
         | NONE => abrupt_result (InvalidCompletion "unbound target") st gas)
    | _ => abrupt_result (InvalidCompletion "bad scalar write") st gas) ∧
  (eval_block n env (IfStmt c ts es :: ss) st gas =
    case eval_atom st.scopes c of
      SOME (ScalarValue (BoolValue b)) =>
        let r = pop_result (eval_block n env (if b then ts else es)
                              (push_scope st) gas) in
        if r.completion = NormalCompletion
        then eval_block n env ss r.state r.unused_gas_evidence
        else r
    | _ => abrupt_result (InvalidCompletion "non-boolean condition") st gas) ∧
  (eval_block n env (WhileStmt prelude c body :: ss) st gas =
    let r1 = eval_block n env prelude (push_scope st) gas in
    if r1.completion ≠ NormalCompletion then pop_result r1 else
    case eval_atom r1.state.scopes c of
      SOME (ScalarValue (BoolValue F)) =>
        eval_block n env ss (pop_result r1).state r1.unused_gas_evidence
    | SOME (ScalarValue (BoolValue T)) =>
        let r2 = pop_result (eval_block n env body r1.state
                               r1.unused_gas_evidence) in
        (case r2.completion of
           BreakCompletion =>
             eval_block n env ss r2.state r2.unused_gas_evidence
         | NormalCompletion =>
             if n = 0 then r2 with completion := FuelExhausted else
             let r3 = eval_block (n - 1) env [WhileStmt prelude c body]
                        r2.state r2.unused_gas_evidence in
             if r3.completion = NormalCompletion
             then eval_block n env ss r3.state r3.unused_gas_evidence
             else r3
         | ContinueCompletion =>
             if n = 0 then r2 with completion := FuelExhausted else
             let r3 = eval_block (n - 1) env [WhileStmt prelude c body]
                        r2.state r2.unused_gas_evidence in
             if r3.completion = NormalCompletion
             then eval_block n env ss r3.state r3.unused_gas_evidence
             else r3
         | _ => r2)
    | _ =>
        pop_result
          (abrupt_result (InvalidCompletion "non-boolean condition")
             r1.state r1.unused_gas_evidence)) ∧
  (eval_block n env (ReturnStmt atoms :: ss) st gas =
    case eval_atoms st.scopes atoms of
      SOME vs => abrupt_result (ReturnCompletion vs) st gas
    | NONE => abrupt_result (InvalidCompletion "unbound atom") st gas) ∧
  (eval_block n env (BreakStmt :: ss) st gas =
    abrupt_result BreakCompletion st gas) ∧
  (eval_block n env (ContinueStmt :: ss) st gas =
    abrupt_result ContinueCompletion st gas) ∧
  (eval_block n env (RevertStmt a :: ss) st gas =
    case eval_atom st.scopes a of
      SOME (ScalarValue (BytesValue data)) =>
        abrupt_result (RevertCompletion data) st gas
    | _ => abrupt_result (InvalidCompletion "bad revert payload") st gas) ∧
  (eval_block n env (_ :: ss) st gas =
    abrupt_result (InvalidCompletion "unsupported statement") st gas) ∧
  (* A successful call completes with ReturnCompletion of the returned values,
   * whether the body returned explicitly or fell through.
   *)
  (invoke_source n env f args st gas =
    if n = 0 then abrupt_result FuelExhausted st gas else
    case lookup_procedure env f of
      NONE => abrupt_result (InvalidCompletion "unknown procedure") st gas
    | SOME p =>
        case entry_scope env p args of
          NONE => abrupt_result (InvalidCompletion "bad arguments") st gas
        | SOME scope =>
            let r = eval_block (n - 1) env p.body
                      (st with <| scopes := [scope]; targets := [] |>) gas in
            let st' = r.state with <| scopes := st.scopes;
                                      targets := st.targets |> in
            let c =
              case r.completion of
                NormalCompletion =>
                  (case read_returns r.state.scopes p.return_bindings of
                     SOME vs => ReturnCompletion vs
                   | NONE => InvalidCompletion "missing return binding")
              | BreakCompletion => InvalidCompletion "break escaped procedure"
              | ContinueCompletion =>
                  InvalidCompletion "continue escaped procedure"
              | other => other in
            abrupt_result c st' r.unused_gas_evidence)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<)
    (λx. case x of
           INL (n, env, ss, st, gas) => (n, core_stmt1_size ss)
         | INR (n, env, f, args, st, gas) => (n, 0))’ >>
  rw[solidityCoreTheory.core_stmt_size_def]
End

(* cv translation, so core programs run under cv_compute. Termination of the
 * translated evaluator follows the same (fuel, statement size) order, read off
 * the cv encodings.
 *)

Theorem cv_fuel_lt[local]:
  cv$c2b (cv_lt (cv$Num 0) n) ⇒ cv$c2n (cv_sub n (cv$Num 1)) < cv$c2n n
Proof
  Cases_on ‘n’ >> rw[]
QED

Theorem cv_size_fst_le[local]:
  cv_size (cv_fst x) ≤ cv_size x
Proof
  Cases_on ‘x’ >> rw[]
QED

Theorem cv_size_snd_le[local]:
  cv_size (cv_snd x) ≤ cv_size x
Proof
  Cases_on ‘x’ >> rw[]
QED

Theorem cv_size_pair_lt[local]:
  cv$c2b (cv_ispair x) ⇒
  0 < cv_size x ∧ cv_size (cv_fst x) < cv_size x ∧
  cv_size (cv_snd x) < cv_size x
Proof
  Cases_on ‘x’ >> rw[]
QED

local
  fun is_cv_proj t =
    is_comb t andalso
    let val f = rator t
    in same_const f “cv_fst” orelse same_const f “cv_snd” end
  fun proj_fact t =
    if same_const (rator t) “cv_fst” then SPEC (rand t) (GEN_ALL cv_size_fst_le)
    else SPEC (rand t) (GEN_ALL cv_size_snd_le)
in
  fun cv_size_tac (asl, w) =
    (MAP_EVERY (assume_tac o proj_fact) (find_terms is_cv_proj w) >>
     imp_res_tac cv_size_pair_lt >> decide_tac) (asl, w)
end

val () = cv_auto_trans_rec eval_block_def (
  WF_REL_TAC ‘inv_image ($< LEX $<)
    (λx. case x of
           INL (n, env, ss, st, gas) => (cv$c2n n, cv_size ss)
         | INR (n, env, f, args, st, gas) => (cv$c2n n, 0))’ >>
  rpt strip_tac >> gvs[] >>
  TRY (metis_tac[cv_fuel_lt] >> NO_TAC) >>
  TRY (cv_size_tac >> NO_TAC) >>
  IF_CASES_TAC >> cv_size_tac
);
