(* Evaluator: locals, value-type state variables, control flow and internal
 * calls over the core, fuel-indexed by recursive depth.
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
 * Storage: a state variable lives in the storage of the executing account,
 * frame.self_address, in the world's verifereum accounts, at the slot and
 * byte offset of the program's layout. Reads and writes go straight to that
 * world, so a write is seen by everything after it, callers and callees
 * included; restoring the world on revert is the frame's job
 * (finish_source_frame). Access sets and original values, which only matter
 * to gas, are not tracked.
 *
 * Gas evidence is passed through unchanged; the EVM boundary is out of scope.
 * Unsupported statements and operations, and anything the checker would reject,
 * end in InvalidCompletion.
 *)
Theory solidityEvaluator
Ancestors
  solidityState solidityScalar vfmCompute keccak
Libs
  cv_transLib wordsLib intLib

(* Scopes and targets *)

Definition ast_key_def:
  ast_key (AstId n) = n
End

Definition lookup_binding_def:
  (lookup_binding x [] = NONE) ∧
  (lookup_binding x (scope :: scopes) =
    case FLOOKUP scope (ast_key x) of
      SOME b => SOME b
    | NONE => lookup_binding x scopes)
End

(* Writes the binding in the innermost scope that holds it. *)
Definition update_binding_def:
  (update_binding x v [] = NONE) ∧
  (update_binding x v (scope :: scopes) =
    case FLOOKUP scope (ast_key x) of
      SOME b =>
        SOME ((scope |+ (ast_key x, b with binding_value := v)) :: scopes)
    | NONE =>
        (case update_binding x v scopes of
           SOME scopes' => SOME (scope :: scopes')
         | NONE => NONE))
End

Definition bind_local_def:
  (bind_local x b [] = [FEMPTY |+ (ast_key x, b)]) ∧
  (bind_local x b (scope :: scopes) = (scope |+ (ast_key x, b)) :: scopes)
End

Definition set_target_def:
  set_target t target targets = targets |+ (ast_key t, target)
End

Definition push_scope_def:
  push_scope (st : source_state) = st with scopes := FEMPTY :: st.scopes
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

(* Every operation except a state read and an internal call. *)
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
             (case oEL n vs of
                SOME v => ValueOk v
              | NONE => ValueAbrupt (InvalidCompletion "tuple index"))
         | _ => ValueAbrupt (InvalidCompletion "not a tuple"))
    | _ => ValueAbrupt (InvalidCompletion "unsupported operation")
End

(* Storage *)

(* A value as the number held in its b storage bytes: integers in two's
 * complement, fixed bytes big-endian.
 *)
Definition stored_number_def:
  stored_number b s =
    case s of
      BoolValue v => SOME (if v then 1 else 0)
    | IntegerValue i => SOME (Num (wrap_integer F (8 * b) i))
    | AddressValue a => SOME (w2n a)
    | BytesValue bs => SOME (num_of_be_bytes bs)
    | _ => NONE
End

(* The value of type ty held as the number n < 256 ** storage_bytes ty. *)
Definition stored_value_def:
  stored_value ty (n : num) =
    case ty of
      BoolT => SOME (BoolValue (n ≠ 0))
    | UintT _ => SOME (IntegerValue (&n))
    | IntT w => SOME (IntegerValue (wrap_integer T w (&n)))
    | AddressT _ => SOME (AddressValue (n2w n))
    | FixedBytesT k => SOME (BytesValue (num_to_bytes k n))
    | _ => NONE
End

(* The bytes of a value of type ty at a byte offset from the low-order end of
 * a slot of an account. Reading keeps only those bytes, as the compiler's
 * storage cleanup does; writing replaces only them.
 *)
Definition read_storage_def:
  read_storage accounts addr slot offset ty =
    case storage_bytes ty of
      SOME b =>
        stored_value ty
          ((w2n (lookup_storage slot (lookup_account addr accounts).storage)
            DIV 2 ** (8 * offset)) MOD 2 ** (8 * b))
    | NONE => NONE
End

Definition write_storage_def:
  write_storage accounts addr slot offset ty s =
    case storage_bytes ty of
      NONE => NONE
    | SOME b =>
        case stored_number b s of
          NONE => NONE
        | SOME v =>
            let account = lookup_account addr accounts in
            let w = w2n (lookup_storage slot account.storage) in
            let lo = 2 ** (8 * offset) in
            let hi = 2 ** (8 * (offset + b)) in
            let w' = w DIV hi * hi + v MOD 2 ** (8 * b) * lo + w MOD lo in
            SOME (update_account addr
                    (account with storage :=
                       update_storage slot (n2w w') account.storage)
                    accounts)
End

Definition read_state_variable_def:
  read_state_variable env (st : source_state) x =
    case lookup_state_variable env x of
      SOME v =>
        read_storage st.world.accounts st.frame.self_address v.state_slot
          v.state_offset v.state_type
    | NONE => NONE
End

(* A state variable's location in the executing account. A value type needs
 * no layout for navigation; its layout id names the declaration.
 *)
Definition state_target_def:
  state_target env (st : source_state) x =
    case lookup_state_variable env x of
      SOME v =>
        SOME (ValueTarget
                (StorageReference PersistentStorage st.frame.self_address
                   v.state_slot v.state_offset v.state_type
                   (LayoutId (ast_key x))))
    | NONE => NONE
End

(* Solidity mapping keys occupy one 32-byte word: integers are extended to
 * 256 bits, addresses and booleans are zero padded, bytesN are right padded.
 *)
Definition mapping_key_bytes_def:
  mapping_key_bytes key s =
    if ¬elementary_storage_type_ok key ∨ ¬elementary_scalar_has_type key s then NONE
    else case s of
      BytesValue bs => SOME (bs ++ REPLICATE (32 - LENGTH bs) 0w)
    | _ => OPTION_MAP (num_to_bytes 32) (stored_number 32 s)
End

Definition mapping_slot_def:
  mapping_slot key_bytes (slot : bytes32) : bytes32 =
    word_of_bytes_be (Keccak_256_w64 (key_bytes ++ num_to_bytes 32 (w2n slot)))
End

(* Navigation consumes already evaluated atoms and returns a concrete location.
 * A nested mapping starts at the preceding mapping's hashed slot.
 *)
Definition navigate_storage_def:
  navigate_storage r s =
    case r of
      StorageReference PersistentStorage addr slot 0 (MappingT key value) layout =>
        (case mapping_key_bytes key s of
           SOME bs =>
             ValueOk (ReferenceValue
               (StorageReference PersistentStorage addr (mapping_slot bs slot)
                  0 value layout))
         | NONE => ValueAbrupt (InvalidCompletion "bad mapping key"))
    | _ => ValueAbrupt (InvalidCompletion "unsupported storage navigation")
End

(* Every operation except an internal call, which needs the evaluator. *)
Definition eval_operation_def:
  eval_operation env (st : source_state) op =
    case op of
      ReadStateOperation x =>
        (case read_state_variable env st x of
           SOME s => ValueOk (ScalarValue s)
         | NONE => ValueAbrupt (InvalidCompletion "bad state read"))
    | StateReferenceOperation x =>
        (case state_target env st x of
           SOME (ValueTarget r) => ValueOk (ReferenceValue r)
         | _ => ValueAbrupt (InvalidCompletion "bad state reference"))
    | ReadOperation ty a =>
        (case eval_atom st.scopes a of
           SOME (ReferenceValue
             (StorageReference PersistentStorage addr slot offset rty _)) =>
               if rty ≠ ty then ValueAbrupt (InvalidCompletion "bad read type")
               else (case read_storage st.world.accounts addr slot offset ty of
                       SOME s => ValueOk (ScalarValue s)
                     | NONE => ValueAbrupt (InvalidCompletion "bad storage read"))
         | _ => ValueAbrupt (InvalidCompletion "bad storage reference"))
    | NavigateOperation ty root_expr (IndexNavigation index) =>
        (case (eval_atom st.scopes root_expr, eval_atom st.scopes index) of
           (SOME (ReferenceValue r), SOME (ScalarValue s)) =>
             navigate_storage r s
         | _ => ValueAbrupt (InvalidCompletion "bad index operands"))
    | _ => eval_pure_operation env st.scopes op
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
  (bind_parameters [] [] = SOME FEMPTY) ∧
  (bind_parameters ((x, ty) :: params) (v :: vs) =
    case bind_parameters params vs of
      SOME scope => SOME (scope |+ (ast_key x, single_binding ty v))
    | NONE => NONE) ∧
  (bind_parameters _ _ = NONE)
End

Definition bind_defaults_def:
  (bind_defaults env [] = SOME FEMPTY) ∧
  (bind_defaults env ((x, ty) :: rets) =
    case (default_scalar env ty, bind_defaults env rets) of
      (SOME s, SOME scope) =>
        SOME (scope |+ (ast_key x, single_binding ty (ScalarValue s)))
    | _ => NONE)
End

(* Parameters bound to arguments, return bindings default-initialised. *)
Definition entry_scope_def:
  entry_scope env (p : core_procedure) args =
    case (bind_parameters p.parameters args, bind_defaults env p.return_bindings)
    of
      (SOME params, SOME rets) => SOME (FUNION params rets)
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

(* Statements that do not run nested code *)

Definition define_binding_def:
  define_binding x ty v (st : source_state) =
    st with scopes :=
      bind_local x <| binding_type := ty; binding_value := v |> st.scopes
End

(* A storage write in a static frame fails; the EVM would halt exceptionally,
 * which no source completion models yet.
 *)
Definition write_target_def:
  write_target t a (st : source_state) =
    case (FLOOKUP st.targets (ast_key t), eval_atom st.scopes a) of
      (SOME (BindTarget x), SOME v) =>
        (case update_binding x v st.scopes of
           SOME scopes => SOME (st with scopes := scopes)
         | NONE => NONE)
    | (SOME (ValueTarget (StorageReference PersistentStorage addr slot offset
                            ty _)), SOME (ScalarValue s)) =>
        if st.frame.static_context then NONE else
        (case write_storage st.world.accounts addr slot offset ty s of
           SOME accounts =>
             SOME (st with world := st.world with accounts := accounts)
         | NONE => NONE)
    | _ => NONE
End

(* Every statement except internal calls, if and while. *)
Definition simple_stmt_def:
  simple_stmt env s st gas =
    case s of
      DefineStmt x ty op =>
        (case eval_operation env st op of
           ValueOk v => normal_result (define_binding x ty v st) gas
         | ValueAbrupt c => abrupt_result c st gas)
    | CaptureBindingStmt t x =>
        normal_result
          (st with targets := set_target t (BindTarget x) st.targets) gas
    | CaptureValueStmt t a =>
        (case eval_atom st.scopes a of
           SOME (ReferenceValue r) =>
             normal_result
               (st with targets := set_target t (ValueTarget r) st.targets) gas
         | _ => abrupt_result (InvalidCompletion "bad captured reference") st gas)
    | CaptureStateStmt t x =>
        (case state_target env st x of
           SOME target =>
             normal_result
               (st with targets := set_target t target st.targets) gas
         | NONE =>
             abrupt_result (InvalidCompletion "unknown state variable") st gas)
    | WriteScalarStmt t ty a =>
        (case write_target t a st of
           SOME st' => normal_result st' gas
         | NONE => abrupt_result (InvalidCompletion "bad scalar write") st gas)
    | ReturnStmt atoms =>
        (case eval_atoms st.scopes atoms of
           SOME vs => abrupt_result (ReturnCompletion vs) st gas
         | NONE => abrupt_result (InvalidCompletion "unbound atom") st gas)
    | BreakStmt => abrupt_result BreakCompletion st gas
    | ContinueStmt => abrupt_result ContinueCompletion st gas
    | RevertStmt a =>
        (case eval_atom st.scopes a of
           SOME (ScalarValue (BytesValue data)) =>
             abrupt_result (RevertCompletion data) st gas
         | _ => abrupt_result (InvalidCompletion "bad revert payload") st gas)
    | _ => abrupt_result (InvalidCompletion "unsupported statement") st gas
End

(* Pieces of the recursive cases *)

Definition branch_of_def:
  branch_of (st : source_state) c =
    case eval_atom st.scopes c of
      SOME (ScalarValue (BoolValue b)) => SOME b
    | _ => NONE
End

(* A call's returned values, packed per call_result_type, bound to x. *)
Definition bind_call_result_def:
  bind_call_result x ty (r : source_result) =
    case r.completion of
      ReturnCompletion vs =>
        normal_result (define_binding x ty (pack_results vs) r.state)
          r.unused_gas_evidence
    | _ => r
End

Datatype:
  loop_step = LoopExit | LoopNext | LoopStop
End

(* After a loop body: break leaves the loop normally, normal completion and
 * continue go round again, anything else propagates.
 *)
Definition loop_after_body_def:
  loop_after_body c =
    case c of
      BreakCompletion => LoopExit
    | NormalCompletion => LoopNext
    | ContinueCompletion => LoopNext
    | _ => LoopStop
End

Definition enter_procedure_def:
  enter_procedure (st : source_state) scope =
    st with <| scopes := [scope]; targets := FEMPTY |>
End

Definition restore_caller_def:
  restore_caller (caller : source_state) (callee : source_state) =
    callee with <| scopes := caller.scopes; targets := caller.targets |>
End

(* A body's completion as the call's: falling through returns the current
 * return bindings, and break/continue cannot escape a procedure.
 *)
Definition procedure_completion_def:
  procedure_completion (p : core_procedure) (r : source_result) =
    case r.completion of
      NormalCompletion =>
        (case read_returns r.state.scopes p.return_bindings of
           SOME vs => ReturnCompletion vs
         | NONE => InvalidCompletion "missing return binding")
    | BreakCompletion => InvalidCompletion "break escaped procedure"
    | ContinueCompletion => InvalidCompletion "continue escaped procedure"
    | c => c
End

(* The evaluator *)

Definition eval_block_def:
  (eval_block (n : num) env [] st gas = normal_result st gas) ∧
  (eval_block n env (s :: ss) st gas =
    let r = eval_stmt n env s st gas in
    if r.completion = NormalCompletion
    then eval_block n env ss r.state r.unused_gas_evidence
    else r) ∧
  (eval_stmt n env (DefineStmt x ty (InternalCallOperation f atoms)) st gas =
    case eval_atoms st.scopes atoms of
      SOME args => bind_call_result x ty (invoke_source n env f args st gas)
    | NONE => abrupt_result (InvalidCompletion "unbound atom") st gas) ∧
  (eval_stmt n env (IfStmt c ts es) st gas =
    case branch_of st c of
      SOME T => pop_result (eval_block n env ts (push_scope st) gas)
    | SOME F => pop_result (eval_block n env es (push_scope st) gas)
    | NONE =>
        abrupt_result (InvalidCompletion "non-boolean condition") st gas) ∧
  (eval_stmt n env (WhileStmt prelude c body) st gas =
    eval_loop n env prelude c body st gas) ∧
  (eval_stmt n env s st gas = simple_stmt env s st gas) ∧
  (* One iteration in a pushed scope; fuel is spent on the back edge. *)
  (eval_loop n env prelude c body st gas =
    let r1 = eval_block n env prelude (push_scope st) gas in
    if r1.completion ≠ NormalCompletion then pop_result r1 else
    case branch_of r1.state c of
      NONE =>
        pop_result
          (r1 with completion := InvalidCompletion "non-boolean condition")
    | SOME b =>
        if ¬b then pop_result r1 else
        let r2 = pop_result (eval_block n env body r1.state
                               r1.unused_gas_evidence) in
        case loop_after_body r2.completion of
          LoopExit => r2 with completion := NormalCompletion
        | LoopStop => r2
        | LoopNext =>
            if n = 0 then r2 with completion := FuelExhausted
            else eval_loop (n - 1) env prelude c body r2.state
                   r2.unused_gas_evidence) ∧
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
            let r = eval_block (n - 1) env p.body (enter_procedure st scope)
                      gas in
            abrupt_result (procedure_completion p r)
              (restore_caller st r.state) r.unused_gas_evidence)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<)
    (λx. case x of
           INL (n, env, ss, st, gas) => (n, list_size core_stmt_size ss)
         | INR (INL (n, env, s, st, gas)) => (n, core_stmt_size s)
         | INR (INR (INL (n, env, pre, c, bd, st, gas))) =>
             (n, list_size core_stmt_size pre +
                 list_size core_stmt_size bd + 1)
         | INR (INR (INR (n, env, f, args, st, gas))) => (n, 0))’ >>
  rw[solidityCoreTheory.core_stmt_size_def, listTheory.list_size_def] >>
  rename1 ‘core_atom_size a’ >> Cases_on ‘a’ >>
  simp[solidityCoreTheory.core_atom_size_def]
End

(* cv translation, so core programs run under cv_compute. Termination of the
 * translated evaluator follows a scaled (fuel, size) order on the cv encodings,
 * strictly decreasing on every cv input.
 *)

val () = cv_auto_trans simple_stmt_def;
val () = cv_auto_trans bind_call_result_def;
val () = cv_auto_trans procedure_completion_def;

val () = cv_auto_trans_rec eval_block_def (
  WF_REL_TAC ‘inv_image ($< LEX $<)
    (λx. case x of
           INL (n, env, ss, st, gas) => (cv$c2n n, 2 * cv_size ss)
         | INR (INL (n, env, s, st, gas)) => (cv$c2n n, 2 * cv_size s + 1)
         | INR (INR (INL (n, env, pre, c, bd, st, gas))) =>
             (cv$c2n n, 2 * (cv_size pre + cv_size bd) + 1)
         | INR (INR (INR (n, env, f, args, st, gas))) => (cv$c2n n, 0))’ >>
  cv_termination_tac >>
  (* a while statement's prelude and body against its encoding *)
  rename1 ‘cv_snd (cv_snd x)’ >> Cases_on ‘x’ >> gvs[] >>
  rename1 ‘cv_snd y’ >> Cases_on ‘y’ >> gvs[]
);
