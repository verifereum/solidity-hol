(* Elaboration of the normalised source AST (solidityImport) to the ordered
 * pure core, for the pinned profile solc-0.8.37-via-ir-osaka.
 *
 * Admitted: one contract of pure functions over elementary value types, with
 * locals (including tuple declarations with holes), internal calls with
 * single or multiple returns, explicit elementary conversions, literals,
 * unary, binary, comparison and short-circuit operators, simple and compound
 * assignment to locals, tuple assignment, ++ and --, if, while, do-while,
 * for, break, continue, return and unchecked blocks. Anything else, and any
 * literal that is not an integer, is rejected (NONE) rather than partially
 * elaborated.
 *
 * Schedules, read from the compiler's IR for this profile (the ir output in
 * testdata/frontend/expected/pure_core.json) and checked against the compiled
 * bytecode by the differential tests:
 *  - binary operands, call arguments and tuple components are evaluated left
 *    to right, each read of a local being a copy taken when it is evaluated;
 *  - && and || evaluate their right operand only when needed;
 *  - x op= e evaluates e, then reads x, then writes x;
 *  - ++ and -- read, step (checked unless unchecked) and write back, yielding
 *    the new (prefix) or old (postfix) value;
 *  - a tuple assignment evaluates its right-hand side into fresh values, then
 *    writes the targets from right to left;
 *  - return values and declared variables are converted as the source types
 *    require.
 *
 * Loops: a while condition is elaborated into the loop prelude, which reruns
 * on every iteration. for (init; c; next) body runs init once, then a loop
 * whose prelude runs next on every iteration but the first, then c; so
 * continue reaches next before the condition. do body while (c) is a loop
 * whose prelude evaluates c on every iteration but the first; so continue
 * reaches the condition. A first-iteration flag implements both.
 *
 * Elaboration uses fresh ids above every node id of the unit for temporaries
 * and capture targets. Its output is checked by wf_core_program; it is not
 * proved to be well formed in general.
 *)
Theory solidityElaborate
Ancestors
  solidityImport solidityEvaluator
Libs
  cv_transLib

Datatype:
  elab_ctx = <|
    functions : (num # src_function) list;
    variables : (num # sol_type) list;
    returns : (num # sol_type) list;
    mode : arithmetic_mode
  |>
End

(* Values and conversions *)

(* The type of an elaborated value: an elementary type, an integer literal
 * (whose atom is its value), or several values.
 *)
Datatype:
  elab_type = ElabType sol_type | ElabLiteral | ElabTuple (sol_type list)
End

Definition bind_value_def:
  bind_value (n : num) ty op =
    ([DefineStmt (AstId n) (SingleType ty) op], BoundAtom (AstId n))
End

(* A value of type ty: integer literals stand for themselves, other types are
 * converted.
 *)
Definition coerce_def:
  coerce n ty a vt =
    case vt of
      ElabType src =>
        if src = ty then SOME (([], a), n)
        else SOME (bind_value n ty (ConvertOperation ty a), n + 1)
    | ElabLiteral => if is_integer_type ty then SOME (([], a), n) else NONE
    | ElabTuple _ => NONE
End

(* A copy of a local, so that later writes in the same expression do not
 * change the value already evaluated.
 *)
Definition snapshot_def:
  snapshot n a vt =
    case (a, vt) of
      (BoundAtom _, ElabType ty) =>
        (bind_value n ty (ConvertOperation ty a), n + 1)
    | _ => (([], a), n)
End

Definition assign_local_def:
  assign_local (t : num) x ty a =
    [CaptureBindingStmt (AstId t) (AstId x); WriteScalarStmt (AstId t) ty a]
End

(* Operators *)

Definition arithmetic_operator_def:
  arithmetic_operator op =
    if op = "+" then SOME AddOp
    else if op = "-" then SOME SubtractOp
    else if op = "*" then SOME MultiplyOp
    else if op = "/" then SOME DivideOp
    else if op = "%" then SOME RemainderOp
    else if op = "**" then SOME ExponentOp
    else if op = "<<" then SOME ShiftLeftOp
    else if op = ">>" then SOME ShiftRightOp
    else if op = "&" then SOME BitAndOp
    else if op = "|" then SOME BitOrOp
    else if op = "^" then SOME BitXorOp
    else NONE
End

(* The type of the right operand of an arithmetic operator on type ty. *)
Definition right_operand_type_def:
  right_operand_type op ty =
    if op = ExponentOp ∨ op = ShiftLeftOp ∨ op = ShiftRightOp then UintT 256
    else ty
End

(* The operator of a compound assignment such as "+=". *)
Definition compound_operator_def:
  compound_operator op =
    if op ≠ "=" ∧ isPREFIX "=" (REVERSE op) then
      arithmetic_operator (TAKE (LENGTH op - 1) op)
    else NONE
End

Definition compare_value_def:
  compare_value n ty cop x y =
    bind_value n BoolT (ScalarOperation ty UncheckedArithmetic cop [x; y])
End

Definition negate_value_def:
  negate_value n (ss, a) =
    let (ss', a') = bind_value n BoolT
                      (ScalarOperation BoolT UncheckedArithmetic BoolNotOp [a])
    in ((ss ++ ss', a'), n + 1)
End

(* Comparisons of two operands of type ty, by equality and less-than. *)
Definition comparison_def:
  comparison n ty op al ar =
    if op = "==" then SOME (compare_value n ty EqualOp al ar, n + 1)
    else if op = "!=" then
      SOME (negate_value (n + 1) (compare_value n ty EqualOp al ar))
    else if op = "<" then SOME (compare_value n ty LessThanOp al ar, n + 1)
    else if op = ">" then SOME (compare_value n ty LessThanOp ar al, n + 1)
    else if op = "<=" then
      SOME (negate_value (n + 1) (compare_value n ty LessThanOp ar al))
    else if op = ">=" then
      SOME (negate_value (n + 1) (compare_value n ty LessThanOp al ar))
    else NONE
End

Definition unary_operator_def:
  unary_operator op =
    if op = "-" then SOME NegateOp
    else if op = "~" then SOME BitNotOp
    else if op = "!" then SOME BoolNotOp
    else NONE
End

(* Whether an expression writes a local. *)
Definition expr_assigns_def:
  (expr_assigns (SrcAssignment _ _ _ _ _) ⇔ T) ∧
  (expr_assigns (SrcUnaryOperation _ op _ e _) ⇔
    op = "++" ∨ op = "--" ∨ expr_assigns e) ∧
  (expr_assigns (SrcBinaryOperation _ _ l r _ _) ⇔
    expr_assigns l ∨ expr_assigns r) ∧
  (expr_assigns (SrcTupleExpression _ cs _) ⇔ components_assign cs) ∧
  (expr_assigns (SrcFunctionCall _ _ args _) ⇔ exprs_assign args) ∧
  (expr_assigns (SrcTypeConversion _ _ e _) ⇔ expr_assigns e) ∧
  (expr_assigns _ ⇔ F) ∧
  (components_assign [] ⇔ F) ∧
  (components_assign (NONE :: cs) ⇔ components_assign cs) ∧
  (components_assign (SOME e :: cs) ⇔
    expr_assigns e ∨ components_assign cs) ∧
  (exprs_assign [] ⇔ F) ∧
  (exprs_assign (e :: es) ⇔ expr_assigns e ∨ exprs_assign es)
End

(* The parameter and return types of a callee. *)
Definition callee_types_def:
  callee_types (f : src_function) =
    case (all_some (MAP variable_type f.fn_parameters),
          all_some (MAP variable_type f.fn_returns)) of
      (SOME params, SOME rets) => SOME (params, rets)
    | _ => NONE
End

(* The value of a call, as call_result_type types it. *)
Definition call_value_def:
  (call_value [] = ElabTuple []) ∧
  (call_value [ty] = ElabType ty) ∧
  (call_value tys = ElabTuple tys)
End

(* The components of a multiple-value binding, as fresh bindings. *)
Definition tuple_components_def:
  (tuple_components n r i [] = ([], [], n)) ∧
  (tuple_components n r i (ty :: tys) =
    let (ss, a) = bind_value n ty (TupleComponentOperation i r) in
    let (ss', vs, n') = tuple_components (n + 1) r (i + 1) tys in
    (ss ++ ss', (a, ElabType ty) :: vs, n'))
End

(* Writes of values to the locals of a tuple, right to left. *)
Definition tuple_writes_def:
  (tuple_writes ctx n [] [] = SOME ([], n)) ∧
  (tuple_writes ctx n (NONE :: cs) (_ :: vs) = tuple_writes ctx n cs vs) ∧
  (tuple_writes ctx n (SOME (SrcIdentifier _ _ x _) :: cs) ((a, vt) :: vs) =
    case (ALOOKUP ctx.variables x, tuple_writes ctx n cs vs) of
      (SOME ty, SOME (ws, n')) =>
        (case coerce n' ty a vt of
           SOME ((ss, a'), n'') => SOME (ws ++ ss ++ assign_local n'' x ty a',
                                        n'' + 1)
         | NONE => NONE)
    | _ => NONE) ∧
  (tuple_writes ctx n _ _ = NONE)
End

(* Snapshots of the bound values of a tuple right-hand side. *)
Definition snapshot_values_def:
  (snapshot_values n [] = ([], [], n)) ∧
  (snapshot_values n ((a, vt) :: vs) =
    case snapshot n a vt of
      ((ss, a'), n') =>
        case snapshot_values n' vs of
          (ss', vs', n'') => (ss ++ ss', (a', vt) :: vs', n''))
End

(* Expressions: statements computing a value, the value as an atom, and its
 * decoded type. Multiple values (tuples and calls with several returns) are
 * elaborated by elab_values.
 *)
Definition elab_expr_def:
  (elab_expr ctx n (SrcIdentifier _ _ x _) =
    case ALOOKUP ctx.variables x of
      SOME ty => SOME (([], BoundAtom (AstId x), ElabType ty), n)
    | NONE => NONE) ∧
  (elab_expr ctx n (SrcLiteral _ kind value tid) =
    if kind = "bool" then
      SOME (([], ConstantAtom (BoolValue (value = "true")), ElabType BoolT), n)
    else
      case identifier_integer tid of
        SOME i => SOME (([], ConstantAtom (IntegerValue i), ElabLiteral), n)
      | NONE => NONE) ∧
  (elab_expr ctx n (SrcUnaryOperation _ op prefix e tid) =
    if op = "++" ∨ op = "--" then
      case e of
        SrcIdentifier _ _ x _ =>
          (case ALOOKUP ctx.variables x of
             SOME ty =>
               let (old, old_atom) =
                 bind_value n ty (ConvertOperation ty (BoundAtom (AstId x))) in
               let (step, new_atom) =
                 bind_value (n + 1) ty
                   (ScalarOperation ty ctx.mode
                      (if op = "++" then AddOp else SubtractOp)
                      [BoundAtom (AstId x); ConstantAtom (IntegerValue 1)]) in
               SOME (((if prefix then [] else old) ++ step ++
                      assign_local (n + 2) x ty new_atom,
                      (if prefix then new_atom else old_atom), ElabType ty),
                     n + 3)
           | NONE => NONE)
      | _ => NONE
    else
      case (unary_operator op, identifier_type tid, elab_expr ctx n e) of
        (SOME uop, SOME ty, SOME ((ss, a, vt), n')) =>
          (case coerce n' ty a vt of
             SOME ((cs, a'), n'') =>
               let (ss', v) = bind_value n'' ty
                                (ScalarOperation ty ctx.mode uop [a']) in
               SOME ((ss ++ cs ++ ss', v, ElabType ty), n'' + 1)
           | NONE => NONE)
      | _ => NONE) ∧
  (elab_expr ctx n (SrcBinaryOperation _ op l r common tid) =
    case (identifier_type common, elab_expr ctx n l) of
      (SOME ty, SOME ((sl, al, vl), n1)) =>
        if op = "&&" ∨ op = "||" then
          (case coerce n1 BoolT al vl of
             SOME ((cl, al'), n2) =>
               (case elab_expr ctx (n2 + 2) r of
                  SOME ((sr, ar, vr), n3) =>
                    (case coerce n3 BoolT ar vr of
                       SOME ((cr, ar'), n4) =>
                         let (rs, res) =
                           bind_value n2 BoolT (ConvertOperation BoolT al') in
                         let rhs = sr ++ cr ++
                                   assign_local (n2 + 1) n2 BoolT ar' in
                         SOME ((sl ++ cl ++ rs ++
                                [if op = "&&" then IfStmt res rhs []
                                 else IfStmt res [] rhs],
                                res, ElabType BoolT), n4)
                     | NONE => NONE)
                | NONE => NONE)
           | NONE => NONE)
        else
          (* flat let patterns: nested ones do not cv-translate here *)
          let (copied, n2) =
            if expr_assigns r then snapshot n1 al vl else (([], al), n1) in
          let (sl', al') = copied in
          (case elab_expr ctx n2 r of
             SOME ((sr, ar, vr), n3) =>
               (case arithmetic_operator op of
                  SOME aop =>
                    (case coerce n3 ty al' vl of
                       SOME ((cl, al''), n4) =>
                         (case coerce n4 (right_operand_type aop ty) ar vr of
                            SOME ((cr, ar'), n5) =>
                              let (ss, v) = bind_value n5 ty
                                              (ScalarOperation ty ctx.mode aop
                                                 [al''; ar']) in
                              SOME ((sl ++ sl' ++ sr ++ cl ++ cr ++ ss, v,
                                     ElabType ty), n5 + 1)
                          | NONE => NONE)
                     | NONE => NONE)
                | NONE =>
                    (case coerce n3 ty al' vl of
                       SOME ((cl, al''), n4) =>
                         (case coerce n4 ty ar vr of
                            SOME ((cr, ar'), n5) =>
                              (case comparison n5 ty op al'' ar' of
                                 SOME ((ss, v), n6) =>
                                   SOME ((sl ++ sl' ++ sr ++ cl ++ cr ++ ss, v,
                                          ElabType BoolT), n6)
                               | NONE => NONE)
                          | NONE => NONE)
                     | NONE => NONE))
           | NONE => NONE)
    | _ => NONE) ∧
  (elab_expr ctx n (SrcAssignment _ op (SrcIdentifier _ _ x _) rhs tid) =
    case (ALOOKUP ctx.variables x, elab_expr ctx n rhs) of
      (SOME ty, SOME ((sr, ar, vr), n1)) =>
        if op = "=" then
          (case coerce n1 ty ar vr of
             SOME ((cr, ar'), n2) =>
               SOME ((sr ++ cr ++ assign_local n2 x ty ar', ar', ElabType ty),
                     n2 + 1)
           | NONE => NONE)
        else
          (case compound_operator op of
             SOME aop =>
               (case coerce n1 (right_operand_type aop ty) ar vr of
                  SOME ((cr, ar'), n2) =>
                    let (ss, v) = bind_value n2 ty
                                    (ScalarOperation ty ctx.mode aop
                                       [BoundAtom (AstId x); ar']) in
                    SOME ((sr ++ cr ++ ss ++ assign_local (n2 + 1) x ty v,
                           v, ElabType ty), n2 + 2)
                | NONE => NONE)
           | NONE => NONE)
    | _ => NONE) ∧
  (elab_expr ctx n (SrcAssignment _ op (SrcTupleExpression _ cs _) rhs tid) =
    if op = "=" then
      case elab_values ctx n rhs of
        SOME ((sr, vs), n1) =>
          let (ss, vs', n2) = snapshot_values n1 vs in
          (case tuple_writes ctx n2 cs vs' of
             SOME (ws, n3) =>
               SOME ((sr ++ ss ++ ws, ConstantAtom (BoolValue F),
                      ElabTuple []), n3)
           | NONE => NONE)
      | NONE => NONE
    else NONE) ∧
  (elab_expr ctx n (SrcAssignment _ _ _ _ _) = NONE) ∧
  (elab_expr ctx n (SrcTupleExpression _ [SOME e] _) = elab_expr ctx n e) ∧
  (elab_expr ctx n (SrcTupleExpression _ _ _) = NONE) ∧
  (elab_expr ctx n (SrcFunctionCall _ (SrcIdentifier _ _ f _) args _) =
    case ALOOKUP ctx.functions f of
      SOME callee =>
        (case callee_types callee of
           SOME (params, rets) =>
             (case elab_args ctx n params args of
                SOME ((sa, atoms), n1) =>
                  SOME ((sa ++ [DefineStmt (AstId n1) (call_result_type rets)
                                  (InternalCallOperation (AstId f) atoms)],
                         BoundAtom (AstId n1), call_value rets), n1 + 1)
              | NONE => NONE)
         | NONE => NONE)
    | NONE => NONE) ∧
  (elab_expr ctx n (SrcFunctionCall _ _ _ _) = NONE) ∧
  (elab_expr ctx n (SrcTypeConversion _ tn e _) =
    case (normalize_type_name tn, elab_expr ctx n e) of
      (SOME ty, SOME ((ss, a, vt), n1)) =>
        (case vt of
           ElabTuple _ => NONE
         | _ =>
           let (cs, v) = bind_value n1 ty (ConvertOperation ty a) in
           SOME ((ss ++ cs, v, ElabType ty), n1 + 1))
    | _ => NONE) ∧
  (* Arguments, converted to the parameter types. *)
  (elab_args ctx n [] [] = SOME (([], []), n)) ∧
  (elab_args ctx n (ty :: tys) (e :: es) =
    case elab_expr ctx n e of
      SOME ((ss, a, vt), n1) =>
        let (copied, n2) =
          if exprs_assign es then snapshot n1 a vt else (([], a), n1) in
        let (ss1, a1) = copied in
        (case coerce n2 ty a1 vt of
           SOME ((cs, a2), n3) =>
             (case elab_args ctx n3 tys es of
                SOME ((ss', as), n4) =>
                  SOME ((ss ++ ss1 ++ cs ++ ss', a2 :: as), n4)
              | NONE => NONE)
         | NONE => NONE)
    | NONE => NONE) ∧
  (elab_args ctx n _ _ = NONE) ∧
  (* Multiple values: tuple expressions, and calls with several returns. *)
  (elab_values ctx n e =
    case e of
      SrcTupleExpression _ cs _ =>
        (case cs of
           [SOME e'] => elab_values ctx n e'
         | _ => elab_components ctx n cs)
    | _ =>
      case elab_expr ctx n e of
        SOME ((ss, a, ElabTuple tys), n1) =>
          let (cs, vs, n2) = tuple_components n1 a 0 tys in
          SOME ((ss ++ cs, vs), n2)
      | SOME ((ss, a, vt), n1) => SOME ((ss, [(a, vt)]), n1)
      | NONE => NONE) ∧
  (elab_components ctx n [] = SOME (([], []), n)) ∧
  (elab_components ctx n (SOME e :: cs) =
    case elab_expr ctx n e of
      SOME ((ss, a, vt), n1) =>
        let (copied, n2) =
          if components_assign cs then snapshot n1 a vt else (([], a), n1) in
        let (ss1, a1) = copied in
        (case elab_components ctx n2 cs of
           SOME ((ss', vs), n3) =>
             SOME ((ss ++ ss1 ++ ss', (a1, vt) :: vs), n3)
         | NONE => NONE)
    | NONE => NONE) ∧
  (elab_components ctx n (NONE :: cs) = NONE)
Termination
  WF_REL_TAC ‘measure (λx. case x of
     INL (ctx, n, e) => 2 * src_expr_size e + 1
   | INR (INL (ctx, n, tys, es)) => 2 * list_size src_expr_size es
   | INR (INR (INL (ctx, n, e))) => 2 * src_expr_size e + 2
   | INR (INR (INR (ctx, n, cs))) =>
       2 * list_size (option_size src_expr_size) cs)’ >>
  rw[solidityImportTheory.src_expr_size_def, listTheory.list_size_def,
     basicSizeTheory.option_size_def]
End

(* A boolean condition. *)
Definition elab_condition_def:
  elab_condition ctx n c =
    case elab_expr ctx n c of
      SOME ((ss, a, vt), n1) =>
        (case coerce n1 BoolT a vt of
           SOME ((cs, a'), n2) => SOME ((ss ++ cs, a'), n2)
         | NONE => NONE)
    | NONE => NONE
End

(* Values converted to a list of types, for returns and declarations. *)
Definition coerce_values_def:
  (coerce_values n [] [] = SOME ([], [], n)) ∧
  (coerce_values n (ty :: tys) ((a, vt) :: vs) =
    case coerce n ty a vt of
      SOME ((ss, a'), n1) =>
        (case coerce_values n1 tys vs of
           SOME (ss', as, n2) => SOME (ss ++ ss', a' :: as, n2)
         | NONE => NONE)
    | NONE => NONE) ∧
  (coerce_values n _ _ = NONE)
End

(* The variables of a declaration statement, defined from its values, which
 * are converted to the declared types; holes discard their values.
 *)
Definition declare_values_def:
  (declare_values ctx n [] [] = SOME ([], ctx, n)) ∧
  (declare_values ctx n (NONE :: ds) (_ :: vs) = declare_values ctx n ds vs) ∧
  (declare_values ctx n (SOME (v : src_variable) :: ds) ((a, vt) :: vs) =
    case variable_type v of
      SOME ty =>
        (case coerce n ty a vt of
           SOME ((cs, a'), n1) =>
             (case declare_values
                     (ctx with variables :=
                        (v.var_info.node_id, ty) :: ctx.variables)
                     n1 ds vs of
                SOME (ss, ctx', n2) =>
                  SOME (cs ++ [DefineStmt (AstId v.var_info.node_id)
                                 (SingleType ty) (ConvertOperation ty a')] ++
                        ss, ctx', n2)
              | NONE => NONE)
         | NONE => NONE)
    | NONE => NONE) ∧
  (declare_values ctx n _ _ = NONE)
End

Definition return_atoms_def:
  (return_atoms [] = []) ∧
  (return_atoms ((x, _) :: rs) = BoundAtom (AstId x) :: return_atoms rs)
End

(* A boolean flag set to T, and a write setting it to b. *)
Definition flag_def:
  flag (n : num) =
    DefineStmt (AstId n) (SingleType BoolT)
      (ConvertOperation BoolT (ConstantAtom (BoolValue T)))
End

Definition set_flag_def:
  set_flag (t : num) (n : num) a = assign_local t n BoolT a
End

(* Statements; lists return the context after their declarations. Nested
 * blocks are spliced into the enclosing list: ids are unique, so the core
 * scopes need not mirror the source blocks.
 *)
Definition elab_stmts_def:
  (elab_stmts ctx n [] = SOME (([], ctx), n)) ∧
  (elab_stmts ctx n (st :: ss) =
    case elab_stmt ctx n st of
      SOME ((cs, ctx'), n1) =>
        (case elab_stmts ctx' n1 ss of
           SOME ((cs', ctx''), n2) => SOME ((cs ++ cs', ctx''), n2)
         | NONE => NONE)
    | NONE => NONE) ∧
  (elab_stmt ctx n (SrcBlock _ ss) =
    case elab_stmts ctx n ss of
      SOME ((cs, _), n1) => SOME ((cs, ctx), n1)
    | NONE => NONE) ∧
  (elab_stmt ctx n (SrcUncheckedBlock _ ss) =
    case elab_stmts (ctx with mode := UncheckedArithmetic) n ss of
      SOME ((cs, _), n1) => SOME ((cs, ctx), n1)
    | NONE => NONE) ∧
  (elab_stmt ctx n (SrcExpressionStatement _ e) =
    case elab_expr ctx n e of
      SOME ((ss, _, _), n1) => SOME ((ss, ctx), n1)
    | NONE => NONE) ∧
  (elab_stmt ctx n (SrcVariableDeclarationStatement _ _ [SOME v] NONE) =
    case variable_type v of
      SOME ty =>
        (case default_elementary ty of
           SOME d =>
             SOME (([DefineStmt (AstId v.var_info.node_id) (SingleType ty)
                       (ConvertOperation ty (ConstantAtom d))],
                    ctx with variables :=
                      (v.var_info.node_id, ty) :: ctx.variables), n)
         | NONE => NONE)
    | NONE => NONE) ∧
  (elab_stmt ctx n (SrcVariableDeclarationStatement _ _ decls (SOME e)) =
    case elab_values ctx n e of
      SOME ((ss, vs), n1) =>
        (case declare_values ctx n1 decls vs of
           SOME (ds, ctx', n2) => SOME ((ss ++ ds, ctx'), n2)
         | NONE => NONE)
    | NONE => NONE) ∧
  (elab_stmt ctx n (SrcVariableDeclarationStatement _ _ _ _) = NONE) ∧
  (elab_stmt ctx n (SrcIfStatement _ c t e) =
    case elab_condition ctx n c of
      SOME ((cs, a), n1) =>
        (case elab_stmt ctx n1 t of
           SOME ((ts, _), n2) =>
             (case e of
                NONE => SOME ((cs ++ [IfStmt a ts []], ctx), n2)
              | SOME e =>
                  (case elab_stmt ctx n2 e of
                     SOME ((es, _), n3) =>
                       SOME ((cs ++ [IfStmt a ts es], ctx), n3)
                   | NONE => NONE))
         | NONE => NONE)
    | NONE => NONE) ∧
  (elab_stmt ctx n (SrcWhileStatement _ c bd) =
    case elab_condition ctx n c of
      SOME ((cs, a), n1) =>
        (case elab_stmt ctx n1 bd of
           SOME ((bs, _), n2) => SOME (([WhileStmt cs a bs], ctx), n2)
         | NONE => NONE)
    | NONE => NONE) ∧
  (elab_stmt ctx n (SrcDoWhileStatement _ bd c) =
    (* n: first-iteration flag; n + 1: condition result; n + 2, n + 3: targets *)
    case elab_condition ctx (n + 4) c of
      SOME ((cs, a), n1) =>
        (case elab_stmt ctx n1 bd of
           SOME ((bs, _), n2) =>
             SOME (([flag n; flag (n + 1);
                     WhileStmt
                       ([IfStmt (BoundAtom (AstId n)) []
                           (cs ++ set_flag (n + 2) (n + 1) a)] ++
                        set_flag (n + 3) n (ConstantAtom (BoolValue F)))
                       (BoundAtom (AstId (n + 1))) bs], ctx), n2)
         | NONE => NONE)
    | NONE => NONE) ∧
  (elab_stmt ctx n (SrcForStatement _ ini c nx bd) =
    case elab_for_init ctx n ini of
      SOME ((is, ctx1), n1) =>
        (* n1: first-iteration flag; n1 + 1: its target *)
        (case (case c of
                 NONE => SOME (([], ConstantAtom (BoolValue T)), n1 + 2)
               | SOME c => elab_condition ctx1 (n1 + 2) c) of
           SOME ((cs, a), n2) =>
             (case elab_for_init ctx1 n2 nx of
                SOME ((ns, _), n3) =>
                  (case elab_stmt ctx1 n3 bd of
                     SOME ((bs, _), n4) =>
                       SOME ((is ++
                              [flag n1;
                               WhileStmt
                                 ([IfStmt (BoundAtom (AstId n1)) [] ns] ++
                                  set_flag (n1 + 1) n1
                                    (ConstantAtom (BoolValue F)) ++ cs)
                                 a bs], ctx), n4)
                   | NONE => NONE)
              | NONE => NONE)
         | NONE => NONE)
    | NONE => NONE) ∧
  (elab_stmt ctx n (SrcBreak _) = SOME (([BreakStmt], ctx), n)) ∧
  (elab_stmt ctx n (SrcContinue _) = SOME (([ContinueStmt], ctx), n)) ∧
  (elab_stmt ctx n (SrcReturn _ _ NONE) =
    SOME (([ReturnStmt (return_atoms ctx.returns)], ctx), n)) ∧
  (elab_stmt ctx n (SrcReturn _ _ (SOME e)) =
    case elab_values ctx n e of
      SOME ((ss, vs), n1) =>
        (case coerce_values n1 (MAP SND ctx.returns) vs of
           SOME (cs, as, n2) => SOME ((ss ++ cs ++ [ReturnStmt as], ctx), n2)
         | NONE => NONE)
    | NONE => NONE) ∧
  (* An optional for initialization or loop expression. *)
  (elab_for_init ctx n NONE = SOME (([], ctx), n)) ∧
  (elab_for_init ctx n (SOME st) = elab_stmt ctx n st)
Termination
  WF_REL_TAC ‘measure (λx. case x of
     INL (ctx, n, ss) => list_size src_stmt_size ss
   | INR (INL (ctx, n, st)) => src_stmt_size st
   | INR (INR (ctx, n, st)) => option_size src_stmt_size st)’ >>
  rw[solidityImportTheory.src_stmt_size_def, listTheory.list_size_def,
     basicSizeTheory.option_size_def]
End

(* Functions and units *)

Definition variable_binding_def:
  variable_binding (v : src_variable) =
    case variable_type v of
      SOME ty => SOME (v.var_info.node_id, ty)
    | NONE => NONE
End

Definition core_bindings_def:
  (core_bindings [] = []) ∧
  (core_bindings ((x, ty) :: bs) = (AstId x, ty) :: core_bindings bs)
End

(* A procedure, checked arithmetic by default; parameters and returns keep
 * their declaration ids.
 *)
Definition elab_function_def:
  elab_function functions n (f : src_function) =
    case (all_some (MAP variable_binding f.fn_parameters),
          all_some (MAP variable_binding f.fn_returns), f.fn_body) of
      (SOME ps, SOME rs, SrcBlock _ ss) =>
        (case elab_stmts <| functions := functions; variables := ps ++ rs;
                            returns := rs; mode := CheckedArithmetic |> n ss of
           SOME ((code, _), n1) =>
             SOME (<| procedure_id := AstId f.fn_info.node_id;
                      parameters := core_bindings ps;
                      return_bindings := core_bindings rs;
                      body := code |>, n1)
         | NONE => NONE)
    | _ => NONE
End

Definition elab_functions_def:
  (elab_functions functions n [] = SOME ([], n)) ∧
  (elab_functions functions n (f :: fs) =
    case elab_function functions n f of
      SOME (p, n1) =>
        (case elab_functions functions n1 fs of
           SOME (ps, n2) => SOME (p :: ps, n2)
         | NONE => NONE)
    | NONE => NONE)
End

(* A valid unit of one contract, elaborated with fresh ids above its node ids;
 * the first function is the entry procedure.
 *)
Definition elaborate_unit_def:
  elaborate_unit (u : src_unit) =
    if ¬valid_src_unit u then NONE else
    case u.unit_contracts of
      [c] =>
        (case elab_functions
                (MAP (λf. (f.fn_info.node_id, f)) c.contract_functions)
                (MAX_LIST (unit_ids u) + 1) c.contract_functions of
           SOME (p :: ps, _) =>
             SOME <| procedures := p :: ps; entry_procedure := p.procedure_id |>
         | _ => NONE)
    | _ => NONE
End

(* cv translation, so that units are elaborated by cv_eval. The mutually
 * recursive elaborators terminate on scaled cv sizes of their syntax.
 *)

val () = cv_auto_trans bind_value_def;
val () = cv_auto_trans coerce_def;
val () = cv_auto_trans snapshot_def;
val () = cv_auto_trans assign_local_def;
val () = cv_auto_trans arithmetic_operator_def;
val () = cv_auto_trans right_operand_type_def;
val () = cv_auto_trans compound_operator_def;
val () = cv_auto_trans compare_value_def;
val () = cv_auto_trans negate_value_def;
val () = cv_auto_trans comparison_def;
val () = cv_auto_trans unary_operator_def;
val () = cv_auto_trans callee_types_def;
val () = cv_auto_trans call_value_def;
val () = cv_auto_trans tuple_components_def;
val () = cv_auto_trans tuple_writes_def;
val snapshot_values_pre_def =
  cv_auto_trans_pre "snapshot_values_pre" snapshot_values_def;

Theorem snapshot_values_pre[cv_pre,local]:
  ∀vs n. snapshot_values_pre n vs
Proof
  Induct >> simp[Once snapshot_values_pre_def] >> rw[] >> fs[]
QED

val () = cv_auto_trans_rec expr_assigns_def (
  WF_REL_TAC ‘measure (λx. case x of
                 INL e => cv_size e
               | INR (INL cs) => cv_size cs
               | INR (INR es) => cv_size es)’ >>
  cv_termination_tac
);

val elab_expr_pre_def = cv_auto_trans_pre_rec
  "elab_expr_pre elab_args_pre elab_values_pre elab_components_pre"
  elab_expr_def (
  WF_REL_TAC ‘measure (λx. case x of
     INL (ctx, n, e) => 2 * cv_size e + 1
   | INR (INL (ctx, n, tys, es)) => 2 * cv_size es
   | INR (INR (INL (ctx, n, e))) => 2 * cv_size e + 2
   | INR (INR (INR (ctx, n, cs))) => 2 * cv_size cs)’ >>
  cv_termination_tac
);

Theorem elab_expr_pre[cv_pre,local]:
  (∀ctx n v. elab_expr_pre ctx n v) ∧
  (∀ctx n tys es. elab_args_pre ctx n tys es) ∧
  (∀ctx n e. elab_values_pre ctx n e) ∧
  (∀ctx n cs. elab_components_pre ctx n cs)
Proof
  ho_match_mp_tac elab_expr_ind >> rpt strip_tac >>
  simp[Once elab_expr_pre_def] >> rw[] >> fs[]
QED

val () = cv_auto_trans elab_condition_def;

val coerce_values_pre_def =
  cv_auto_trans_pre "coerce_values_pre" coerce_values_def;

Theorem coerce_values_pre[cv_pre,local]:
  ∀n tys vs. coerce_values_pre n tys vs
Proof
  ho_match_mp_tac coerce_values_ind >> rpt strip_tac >>
  simp[Once coerce_values_pre_def] >> rw[] >> fs[]
QED

val declare_values_pre_def =
  cv_auto_trans_pre "declare_values_pre" declare_values_def;

Theorem declare_values_pre[cv_pre,local]:
  ∀ctx n ds vs. declare_values_pre ctx n ds vs
Proof
  ho_match_mp_tac declare_values_ind >> rpt strip_tac >>
  simp[Once declare_values_pre_def] >> rw[] >> fs[] >>
  (* the record update appears as a case on the context *)
  Cases_on ‘ctx’ >> gvs[fetch "-" "elab_ctx_fn_updates"]
QED

val () = cv_auto_trans return_atoms_def;
val () = cv_auto_trans flag_def;
val () = cv_auto_trans set_flag_def;

val elab_stmts_pre_def = cv_auto_trans_pre_rec
  "elab_stmts_pre elab_stmt_pre elab_for_init_pre" elab_stmts_def (
  WF_REL_TAC ‘measure (λx. case x of
     INL (ctx, n, ss) => cv_size ss
   | INR (INL (ctx, n, st)) => cv_size st
   | INR (INR (ctx, n, st)) => cv_size st)’ >>
  cv_termination_tac
);

Theorem elab_stmts_pre[cv_pre,local]:
  (∀ctx n ss. elab_stmts_pre ctx n ss) ∧
  (∀ctx n st. elab_stmt_pre ctx n st) ∧
  (∀ctx n st. elab_for_init_pre ctx n st)
Proof
  ho_match_mp_tac elab_stmts_ind >> rpt strip_tac >>
  simp[Once elab_stmts_pre_def] >> rw[] >> fs[] >>
  (* the record update appears as a case on the context *)
  Cases_on ‘ctx’ >> gvs[fetch "-" "elab_ctx_fn_updates"]
QED

val () = cv_auto_trans variable_binding_def;
val () = cv_auto_trans core_bindings_def;
val () = cv_auto_trans elab_function_def;
val () = cv_auto_trans elab_functions_def;
val () = cv_auto_trans elaborate_unit_def;
val () = cv_auto_trans solidityCoreWfTheory.core_program_environment_def;
