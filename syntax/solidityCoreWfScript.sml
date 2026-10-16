(* Static environment and well-formedness for the stage-2 pure core.
 *
 * Only the pure fragment is admitted: scalar/convert/tuple/internal-call
 * definitions, local capture and scalar writes, and structured control flow.
 * Reference navigation, reads, copies and external calls are rejected until
 * their validation rules exist (stage 3 onwards).
 *)
Theory solidityCoreWf
Ancestors
  solidityCore alist list option

(* Struct fields are recorded for stage 3; recursive-struct restrictions and
 * layout descriptors are not checked yet.
 *)
Datatype:
  core_type_declaration
  = EnumDeclaration num
  | UserValueDeclaration sol_type
  | StructDeclaration ((ast_id # sol_type) list)
End

Datatype:
  core_environment = <|
    procedures : (ast_id # core_procedure) list;
    type_declarations : (ast_id # core_type_declaration) list;
    layouts : layout_id list
  |>
End

Definition core_program_environment_def:
  core_program_environment decls (prog : core_program) = <|
    procedures := MAP (λp. (p.procedure_id, p)) prog.procedures;
    type_declarations := decls;
    layouts := []
  |>
End

Definition lookup_procedure_def:
  lookup_procedure env f = ALOOKUP env.procedures f
End

Definition lookup_enum_def:
  lookup_enum env id =
    case ALOOKUP env.type_declarations id of
      SOME (EnumDeclaration members) => SOME members
    | _ => NONE
End

Definition lookup_user_value_def:
  lookup_user_value env id =
    case ALOOKUP env.type_declarations id of
      SOME (UserValueDeclaration ty) => SOME ty
    | _ => NONE
End

Definition lookup_struct_def:
  lookup_struct env id =
    case ALOOKUP env.type_declarations id of
      SOME (StructDeclaration fields) => SOME fields
    | _ => NONE
End

(* Types *)

Definition is_elementary_type_def:
  (is_elementary_type BoolT ⇔ T) ∧
  (is_elementary_type (UintT _) ⇔ T) ∧
  (is_elementary_type (IntT _) ⇔ T) ∧
  (is_elementary_type (AddressT _) ⇔ T) ∧
  (is_elementary_type (FixedBytesT _) ⇔ T) ∧
  (is_elementary_type _ ⇔ F)
End

Definition declared_type_ok_def:
  (declared_type_ok env (ArrayT ty _) ⇔ declared_type_ok env ty) ∧
  (declared_type_ok env (MappingT key value) ⇔
    declared_type_ok env key ∧ declared_type_ok env value) ∧
  (declared_type_ok env (StructT id) ⇔ IS_SOME (lookup_struct env id)) ∧
  (declared_type_ok env (EnumT id) ⇔ IS_SOME (lookup_enum env id)) ∧
  (declared_type_ok env (UserValueT id) ⇔ IS_SOME (lookup_user_value env id)) ∧
  (declared_type_ok env (FunctionT _ _ parameters returns) ⇔
    EVERY (declared_type_ok env) parameters ∧
    EVERY (declared_type_ok env) returns) ∧
  (declared_type_ok env (LocatedT _ ty) ⇔ declared_type_ok env ty) ∧
  (declared_type_ok env _ ⇔ T)
Termination
  WF_REL_TAC ‘measure (sol_type_size o SND)’
End

(* Stage 2 bindings, parameters and returns are value types only. *)
Definition core_scalar_type_def:
  core_scalar_type env ty ⇔
    is_value_type ty ∧ valid_type_shape ty ∧ declared_type_ok env ty
End

(* ProductType is reserved for tuples and multiple returns: never singleton. *)
Definition wf_core_value_type_def:
  (wf_core_value_type env (SingleType ty) ⇔ core_scalar_type env ty) ∧
  (wf_core_value_type env (ProductType tys) ⇔
    LENGTH tys ≠ 1 ∧ EVERY (wf_core_value_type env) tys)
Termination
  WF_REL_TAC ‘measure (core_value_type_size o SND)’
End

Definition wf_type_declaration_def:
  (wf_type_declaration (EnumDeclaration members) ⇔
    0 < members ∧ members ≤ 256) ∧
  (wf_type_declaration (UserValueDeclaration ty) ⇔
    is_elementary_type ty ∧ valid_type_shape ty) ∧
  (wf_type_declaration (StructDeclaration fields) ⇔
    fields ≠ [] ∧ ALL_DISTINCT (MAP FST fields) ∧
    EVERY (λ(_, ty). valid_type_shape ty ∧ outer_location_free ty) fields)
End

(* Values *)

Definition elementary_scalar_has_type_def:
  (elementary_scalar_has_type BoolT (BoolValue _) ⇔ T) ∧
  (elementary_scalar_has_type (UintT n) (IntegerValue i) ⇔
    0 ≤ i ∧ i < &(2 ** n)) ∧
  (elementary_scalar_has_type (IntT n) (IntegerValue i) ⇔
    -&(2 ** (n - 1)) ≤ i ∧ i < &(2 ** (n - 1))) ∧
  (elementary_scalar_has_type (AddressT _) (AddressValue _) ⇔ T) ∧
  (elementary_scalar_has_type (FixedBytesT n) (BytesValue bs) ⇔
    LENGTH bs = n) ∧
  (elementary_scalar_has_type _ _ ⇔ F)
End

(* Function mutability is not yet checked against the target procedure. *)
Definition scalar_has_type_def:
  scalar_has_type env ty s ⇔
    case ty of
      EnumT id =>
        (case (lookup_enum env id, s) of
           (SOME members, IntegerValue i) => 0 ≤ i ∧ i < &members
         | _ => F)
    | UserValueT id =>
        (case lookup_user_value env id of
           SOME underlying => elementary_scalar_has_type underlying s
         | NONE => F)
    | ContractT _ =>
        (case s of AddressValue _ => T | _ => F)
    | FunctionT InternalFn _ parameters returns =>
        (case s of
           InternalFunctionValue f =>
             (case lookup_procedure env f of
                SOME p => MAP SND p.parameters = parameters ∧
                          MAP SND p.return_bindings = returns
              | NONE => F)
         | _ => F)
    | FunctionT ExternalFn _ _ _ =>
        (case s of ExternalFunctionValue _ selector => LENGTH selector = 4
                 | _ => F)
    | _ => elementary_scalar_has_type ty s
End

(* Runtime typing seed for the evaluator's progress argument. Reference values
 * are not typed until reference/layout environments exist.
 *)
Definition value_has_type_def:
  (value_has_type env (SingleType ty) (ScalarValue s) ⇔
    scalar_has_type env ty s) ∧
  (value_has_type env (ProductType tys) (TupleValue vs) ⇔
    values_have_types env tys vs) ∧
  (value_has_type env _ _ ⇔ F) ∧
  (values_have_types env [] [] ⇔ T) ∧
  (values_have_types env (ty::tys) (v::vs) ⇔
    value_has_type env ty v ∧ values_have_types env tys vs) ∧
  (values_have_types env _ _ ⇔ F)
End

(* Checking context: bindings and captured targets share one id namespace. *)
Datatype:
  core_check_context = <|
    bindings : (ast_id # core_value_type) list;
    targets : (ast_id # sol_type) list;
    returns : sol_type list;
    in_loop : bool
  |>
End

Definition fresh_core_id_def:
  fresh_core_id ctx x ⇔
    ¬MEM x (MAP FST ctx.bindings) ∧ ¬MEM x (MAP FST ctx.targets)
End

Definition bind_core_id_def:
  bind_core_id x ty ctx = ctx with bindings := (x, ty) :: ctx.bindings
End

Definition capture_core_target_def:
  capture_core_target t ty ctx = ctx with targets := (t, ty) :: ctx.targets
End

(* Constants have no synthesized type, so atoms are checked against one. *)
Definition wf_core_atom_def:
  (wf_core_atom env ctx ty (BoundAtom x) ⇔
    ALOOKUP ctx.bindings x = SOME ty) ∧
  (wf_core_atom env ctx (SingleType ty) (ConstantAtom s) ⇔
    scalar_has_type env ty s) ∧
  (wf_core_atom env ctx (ProductType _) (ConstantAtom _) ⇔ F)
End

(* Operations *)

Definition is_integer_type_def:
  (is_integer_type (UintT _) ⇔ T) ∧
  (is_integer_type (IntT _) ⇔ T) ∧
  (is_integer_type _ ⇔ F)
End

Definition is_bitwise_type_def:
  is_bitwise_type ty ⇔
    is_integer_type ty ∨ (case ty of FixedBytesT _ => T | _ => F)
End

Definition is_ordered_type_def:
  is_ordered_type ty ⇔
    is_integer_type ty ∨
    (case ty of AddressT _ => T | FixedBytesT _ => T | EnumT _ => T | _ => F)
End

Definition is_equality_type_def:
  is_equality_type ty ⇔ ty = BoolT ∨ is_ordered_type ty
End

(* The operation's sol_type is the operand type; comparisons yield BoolT.
 * The arithmetic mode is irrelevant for comparison and bitwise operators.
 *)
Definition scalar_operator_result_def:
  scalar_operator_result op ty =
    case op of
      EqualOp => if is_equality_type ty then SOME BoolT else NONE
    | LessThanOp => if is_ordered_type ty then SOME BoolT else NONE
    | BitAndOp => if is_bitwise_type ty then SOME ty else NONE
    | BitOrOp => if is_bitwise_type ty then SOME ty else NONE
    | BitXorOp => if is_bitwise_type ty then SOME ty else NONE
    | _ => if is_integer_type ty then SOME ty else NONE
End

(* Explicit elementary conversions, including the identity used for moves and
 * default initialization. Truncation/panic behaviour belongs to evaluation.
 *)
Definition elementary_convertible_def:
  elementary_convertible src dst ⇔
    src = dst ∨
    case (src, dst) of
      (UintT _, UintT _) => T
    | (IntT _, IntT _) => T
    | (UintT m, IntT n) => m = n
    | (IntT m, UintT n) => m = n
    | (FixedBytesT _, FixedBytesT _) => T
    | (UintT m, FixedBytesT n) => m = 8 * n
    | (FixedBytesT m, UintT n) => n = 8 * m
    | (AddressT _, AddressT _) => T
    | (AddressT _, UintT n) => n = 160
    | (UintT m, AddressT _) => m = 160
    | (AddressT _, FixedBytesT n) => n = 20
    | (FixedBytesT m, AddressT _) => m = 20
    | (ContractT _, AddressT _) => T
    | (AddressT _, ContractT _) => T
    | (EnumT _, UintT _) => T
    | (UintT _, EnumT _) => T
    | _ => F
End

(* User-defined value types wrap/unwrap through their underlying type. *)
Definition core_convertible_def:
  core_convertible env src dst ⇔
    elementary_convertible src dst ∨
    (case src of
       UserValueT id => lookup_user_value env id = SOME dst
     | _ => F) ∨
    (case dst of
       UserValueT id => lookup_user_value env id = SOME src
     | _ => F)
End

Definition call_result_type_def:
  (call_result_type [] = ProductType []) ∧
  (call_result_type [ty] = SingleType ty) ∧
  (call_result_type tys = ProductType (MAP SingleType tys))
End

Definition wf_core_operation_def:
  (wf_core_operation env ctx annotation
     (ScalarOperation ty mode op args) ⇔
    core_scalar_type env ty ∧ LENGTH args = 2 ∧
    EVERY (wf_core_atom env ctx (SingleType ty)) args ∧
    case scalar_operator_result op ty of
      SOME result => annotation = SingleType result
    | NONE => F) ∧
  (wf_core_operation env ctx annotation (ConvertOperation ty a) ⇔
    annotation = SingleType ty ∧
    case a of
      ConstantAtom s => scalar_has_type env ty s
    | BoundAtom x =>
        (case ALOOKUP ctx.bindings x of
           SOME (SingleType src) => core_convertible env src ty
         | _ => F)) ∧
  (wf_core_operation env ctx annotation (TupleOperation atoms) ⇔
    case annotation of
      ProductType tys => LIST_REL (wf_core_atom env ctx) tys atoms
    | SingleType _ => F) ∧
  (wf_core_operation env ctx annotation (TupleComponentOperation n a) ⇔
    case a of
      BoundAtom x =>
        (case ALOOKUP ctx.bindings x of
           SOME (ProductType tys) => n < LENGTH tys ∧ annotation = EL n tys
         | _ => F)
    | ConstantAtom _ => F) ∧
  (wf_core_operation env ctx annotation (InternalCallOperation f args) ⇔
    case lookup_procedure env f of
      SOME p =>
        LIST_REL (λ(_, ty) a. wf_core_atom env ctx (SingleType ty) a)
          p.parameters args ∧
        annotation = call_result_type (MAP SND p.return_bindings)
    | NONE => F) ∧
  (wf_core_operation env ctx annotation _ ⇔ F)
End

(* Revert payloads are provisional pre-encoded constants until ABI encoding. *)
Definition provisional_revert_payload_def:
  (provisional_revert_payload (ConstantAtom (BytesValue _)) ⇔ T) ∧
  (provisional_revert_payload _ ⇔ F)
End

(* Statements: lexical scopes. A block's definitions extend the context for
 * later statements in that block only; prelude definitions are visible in the
 * loop condition and body. Break/continue are only legal in a loop body, and
 * in_loop does not cross procedure boundaries.
 *)
Definition check_core_stmts_def:
  (check_core_stmts env ctx [] = SOME ctx) ∧
  (check_core_stmts env ctx (DefineStmt x ty op :: ss) =
    if fresh_core_id ctx x ∧ wf_core_value_type env ty ∧
       wf_core_operation env ctx ty op
    then check_core_stmts env (bind_core_id x ty ctx) ss
    else NONE) ∧
  (check_core_stmts env ctx (CaptureBindingStmt t x :: ss) =
    case ALOOKUP ctx.bindings x of
      SOME (SingleType ty) =>
        if fresh_core_id ctx t
        then check_core_stmts env (capture_core_target t ty ctx) ss
        else NONE
    | _ => NONE) ∧
  (check_core_stmts env ctx (WriteScalarStmt t ty a :: ss) =
    if ALOOKUP ctx.targets t = SOME ty ∧
       wf_core_atom env ctx (SingleType ty) a
    then check_core_stmts env ctx ss
    else NONE) ∧
  (check_core_stmts env ctx (IfStmt c ts es :: ss) =
    if wf_core_atom env ctx (SingleType BoolT) c ∧
       IS_SOME (check_core_stmts env ctx ts) ∧
       IS_SOME (check_core_stmts env ctx es)
    then check_core_stmts env ctx ss
    else NONE) ∧
  (check_core_stmts env ctx (WhileStmt prelude c body :: ss) =
    case check_core_stmts env (ctx with in_loop := F) prelude of
      NONE => NONE
    | SOME prelude_ctx =>
        if wf_core_atom env prelude_ctx (SingleType BoolT) c ∧
           IS_SOME (check_core_stmts env (prelude_ctx with in_loop := T) body)
        then check_core_stmts env ctx ss
        else NONE) ∧
  (check_core_stmts env ctx (ReturnStmt atoms :: ss) =
    if LIST_REL (λty a. wf_core_atom env ctx (SingleType ty) a)
         ctx.returns atoms
    then check_core_stmts env ctx ss
    else NONE) ∧
  (check_core_stmts env ctx (BreakStmt :: ss) =
    if ctx.in_loop then check_core_stmts env ctx ss else NONE) ∧
  (check_core_stmts env ctx (ContinueStmt :: ss) =
    if ctx.in_loop then check_core_stmts env ctx ss else NONE) ∧
  (check_core_stmts env ctx (RevertStmt a :: ss) =
    if provisional_revert_payload a then check_core_stmts env ctx ss
    else NONE) ∧
  (check_core_stmts env ctx (_ :: _) = NONE)
Termination
  WF_REL_TAC ‘measure (λ(env, ctx, ss). core_stmt1_size ss)’ >>
  rw[core_stmt_size_def]
End

Definition wf_core_stmts_def:
  wf_core_stmts env ctx ss ⇔ IS_SOME (check_core_stmts env ctx ss)
End

Definition wf_core_stmt_def:
  wf_core_stmt env ctx s ⇔ wf_core_stmts env ctx [s]
End

(* Procedures, environments and programs *)

Definition procedure_check_context_def:
  procedure_check_context (p : core_procedure) = <|
    bindings := MAP (λ(x, ty). (x, SingleType ty))
                  (p.parameters ++ p.return_bindings);
    targets := [];
    returns := MAP SND p.return_bindings;
    in_loop := F
  |>
End

(* Fall-through returns the current return bindings. *)
Definition wf_core_procedure_def:
  wf_core_procedure env (p : core_procedure) ⇔
    ALL_DISTINCT (MAP FST (p.parameters ++ p.return_bindings)) ∧
    EVERY (λ(_, ty). core_scalar_type env ty)
      (p.parameters ++ p.return_bindings) ∧
    wf_core_stmts env (procedure_check_context p) p.body
End

Definition wf_core_environment_def:
  wf_core_environment env ⇔
    ALL_DISTINCT (MAP FST env.procedures) ∧
    EVERY (λ(f, p). p.procedure_id = f ∧ wf_core_procedure env p)
      env.procedures ∧
    ALL_DISTINCT (MAP FST env.type_declarations) ∧
    EVERY (λ(_, decl). wf_type_declaration decl) env.type_declarations
End

Definition wf_core_program_def:
  wf_core_program env (prog : core_program) ⇔
    env.procedures = MAP (λp. (p.procedure_id, p)) prog.procedures ∧
    wf_core_environment env ∧
    IS_SOME (lookup_procedure env prog.entry_procedure)
End

(* Facts the evaluator can use under wf_core_program. *)

Theorem wf_core_environment_lookup:
  wf_core_environment env ∧ lookup_procedure env f = SOME p ⇒
    p.procedure_id = f ∧ wf_core_procedure env p
Proof
  rw[wf_core_environment_def, lookup_procedure_def] >>
  imp_res_tac ALOOKUP_MEM >>
  gvs[EVERY_MEM] >>
  first_x_assum drule >> simp[]
QED

Theorem wf_core_program_lookup:
  wf_core_program env prog ∧ lookup_procedure env f = SOME p ⇒
    p.procedure_id = f ∧ wf_core_procedure env p
Proof
  rw[wf_core_program_def] >> metis_tac[wf_core_environment_lookup]
QED

Theorem wf_core_program_entry:
  wf_core_program env prog ⇒
    ∃p. lookup_procedure env prog.entry_procedure = SOME p ∧
        p.procedure_id = prog.entry_procedure ∧ wf_core_procedure env p
Proof
  rw[wf_core_program_def, IS_SOME_EXISTS] >>
  metis_tac[wf_core_environment_lookup]
QED

Theorem core_program_environment_procedures:
  (core_program_environment decls prog).procedures =
    MAP (λp. (p.procedure_id, p)) prog.procedures
Proof
  simp[core_program_environment_def]
QED