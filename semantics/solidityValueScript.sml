(* Executable helpers for the first ordered-core evaluator. *)
Theory solidityValue
Ancestors
  solidityState vfmCompute vfmState integer arithmetic list finite_map
Libs
  cv_transLib wordsLib

Definition ast_key_def:
  ast_key (AstId n) = n
End

Definition lookup_binding_def:
  lookup_binding id [] = NONE ∧
  lookup_binding id (scope::scopes) =
    case FLOOKUP scope (ast_key id) of
      NONE => lookup_binding id scopes
    | SOME binding => SOME binding
End

Definition replace_binding_def:
  replace_binding id binding [] = NONE ∧
  replace_binding id binding (scope::scopes) =
    if IS_SOME (FLOOKUP scope (ast_key id))
    then SOME ((scope |+ (ast_key id, binding))::scopes)
    else OPTION_MAP (CONS scope) (replace_binding id binding scopes)
End

Definition eval_atom_def:
  eval_atom (ConstantAtom scalar) state = SOME (ScalarValue scalar) ∧
  eval_atom (BoundAtom id) state =
    OPTION_MAP (λbinding. binding.binding_value) (lookup_binding id state.scopes)
End

Definition eval_atoms_def:
  eval_atoms [] state = SOME [] ∧
  eval_atoms (atom::atoms) state =
    case (eval_atom atom state, eval_atoms atoms state) of
      (SOME value, SOME values) => SOME (value::values)
    | _ => NONE
End

Definition integer_bounds_def:
  integer_bounds (UintT n) =
    (if valid_int_width n then SOME ((0:int), (&(2 ** n) - 1:int)) else NONE) ∧
  integer_bounds (IntT n) =
    (if valid_int_width n then SOME ((- &(2 ** (n - 1)):int), (&(2 ** (n - 1)) - 1:int))
    else NONE) ∧
  integer_bounds _ = NONE
End

Definition scalar_matches_def:
  scalar_matches BoolT (BoolValue b) = T ∧
  scalar_matches (UintT n) (IntegerValue i) =
    (valid_int_width n ∧ 0 ≤ i ∧ i < &(2 ** n)) ∧
  scalar_matches (IntT n) (IntegerValue i) =
    (valid_int_width n ∧ - &(2 ** (n - 1)) ≤ i ∧ i < &(2 ** (n - 1))) ∧
  scalar_matches (AddressT p) (AddressValue a) = T ∧
  scalar_matches (FixedBytesT n) (BytesValue bytes) =
    (valid_fixed_bytes_width n ∧ LENGTH bytes = n) ∧
  scalar_matches _ _ = F
End

Definition reference_matches_def:
  reference_matches (LocatedT StorageLoc ty)
    (StorageReference backend address slot offset actual layout) = (ty = actual) ∧
  reference_matches (LocatedT MemoryLoc ty) (MemoryReference object offset actual) =
    (ty = actual) ∧
  reference_matches (LocatedT CalldataLoc ty) (CalldataReference offset length actual) =
    (ty = actual) ∧
  reference_matches _ _ = F
End

Definition single_matches_def:
  single_matches ty (ScalarValue scalar) = scalar_matches ty scalar ∧
  single_matches ty (ReferenceValue reference) = reference_matches ty reference ∧
  single_matches ty _ = F
End

(* A structurally terminating worklist, not source-fuelled tuple checking. *)
Definition values_match_def:
  values_match [] [] = T ∧
  values_match (SingleType ty::types) (value::values) =
    (single_matches ty value ∧ values_match types values) ∧
  values_match (ProductType components::types) (TupleValue fields::values) =
    (LENGTH components = LENGTH fields ∧
     values_match (components ++ types) (fields ++ values)) ∧
  values_match _ _ = F
Termination
  WF_REL_TAC ‘measure (list_size core_value_type_size o FST)’
  \\ simp[]
End

Definition default_scalar_def:
  default_scalar BoolT = SOME (BoolValue F) ∧
  default_scalar (UintT n) =
    (if valid_int_width n then SOME (IntegerValue 0) else NONE) ∧
  default_scalar (IntT n) =
    (if valid_int_width n then SOME (IntegerValue 0) else NONE) ∧
  default_scalar (AddressT p) = SOME (AddressValue 0w) ∧
  default_scalar (FixedBytesT n) =
    (if valid_fixed_bytes_width n then SOME (BytesValue (REPLICATE n 0w)) else NONE) ∧
  default_scalar _ = NONE
End

Definition scalar_result_def:
  scalar_result ty mode i =
    case integer_bounds ty of
      NONE => INL (InvalidCompletion "invalid integer type")
    | SOME (lo, hi) =>
        if hi - lo + 1 ≤ 0 then INL (InvalidCompletion "invalid integer bounds") else
        if mode = CheckedArithmetic ∧ (i < lo ∨ hi < i)
        then INL (PanicCompletion 17)
        else INR (ScalarValue (IntegerValue ((i - lo) % (hi - lo + 1) + lo)))
End

(* Solidity division truncates towards zero; HOL's integer / rounds down. *)
Definition trunc_div_def:
  trunc_div (a:int) (b:int) =
    if ABS b = 0 then 0 else
    let q = ABS a / ABS b in
      if (a < 0) ≠ (b < 0) then -q else q
End

Definition eval_scalar_operation_def:
  eval_scalar_operation ty mode op values =
    if ¬EVERY (single_matches ty) values
    then INL (InvalidCompletion "scalar operand type mismatch")
    else case (op, values) of
      (EqualOp, [ScalarValue a; ScalarValue b]) => INR (ScalarValue (BoolValue (a = b)))
    | (LessThanOp, [ScalarValue (IntegerValue a); ScalarValue (IntegerValue b)]) =>
        INR (ScalarValue (BoolValue (a < b)))
    | (AddOp, [ScalarValue (IntegerValue a); ScalarValue (IntegerValue b)]) =>
        scalar_result ty mode (a + b)
    | (SubtractOp, [ScalarValue (IntegerValue a); ScalarValue (IntegerValue b)]) =>
        scalar_result ty mode (a - b)
    | (MultiplyOp, [ScalarValue (IntegerValue a); ScalarValue (IntegerValue b)]) =>
        scalar_result ty mode (a * b)
    | (DivideOp, [ScalarValue (IntegerValue a); ScalarValue (IntegerValue b)]) =>
        if b = 0 then INL (PanicCompletion 18) else scalar_result ty mode (trunc_div a b)
    | (RemainderOp, [ScalarValue (IntegerValue a); ScalarValue (IntegerValue b)]) =>
        if b = 0 then INL (PanicCompletion 18)
        else scalar_result ty mode (a - trunc_div a b * b)
    | _ => INL (InvalidCompletion "unsupported scalar operation")
End

Definition define_binding_def:
  define_binding id ty value state =
    if ¬values_match [ty] [value] ∨ IS_SOME (lookup_binding id state.scopes)
    then NONE
    else case state.scopes of
      [] => NONE
    | scope::scopes => SOME (state with scopes :=
        (scope |+ (ast_key id, <| binding_type := ty;
          binding_value := value; binding_assignable := T |>))::scopes)
End

Definition assign_binding_def:
  assign_binding id ty value state =
    case lookup_binding id state.scopes of
      NONE => NONE
    | SOME binding =>
        if ¬binding.binding_assignable ∨ binding.binding_type ≠ SingleType ty ∨
           ¬single_matches ty value then NONE
        else OPTION_MAP (λscopes. state with scopes := scopes)
          (replace_binding id (binding with binding_value := value) state.scopes)
End

Definition read_memory_def:
  read_memory ty (MemoryReference (HeapId id) offset actual) state =
    (if ty ≠ actual then NONE else
    case FLOOKUP state.heap id of
      NONE => NONE
    | SOME object =>
        if object.object_length ≤ offset then NONE else
        case FLOOKUP object.object_cells offset of
          NONE => NONE
        | SOME value => if single_matches ty value then SOME value else NONE) ∧
  read_memory ty _ state = NONE
End

Definition write_memory_def:
  write_memory ty (MemoryReference (HeapId id) offset actual) value state =
    (if ty ≠ actual ∨ ¬single_matches ty value then NONE else
    case FLOOKUP state.heap id of
      NONE => NONE
    | SOME object =>
        if object.object_length ≤ offset then NONE else
        SOME (state with heap := state.heap |+ (id,
          object with object_cells := object.object_cells |+ (offset, value)))) ∧
  write_memory ty _ value state = NONE
End

Definition write_target_def:
  write_target reference_write target ty value state =
    if reference_write then
      (case value of
         ReferenceValue reference =>
           (case target of
              BindTarget id => assign_binding id ty value state
            | ReferenceFieldTarget id offset actual =>
                write_memory ty (MemoryReference id offset actual) value state
            | _ => NONE)
       | _ => NONE)
    else (case value of
       ScalarValue scalar =>
         (case target of
            BindTarget id => assign_binding id ty value state
          | ValueTarget reference => write_memory ty reference value state
          | _ => NONE)
     | _ => NONE)
End

val () = List.app cv_auto_trans
  [ast_key_def, lookup_binding_def, replace_binding_def, eval_atom_def,
   eval_atoms_def, integer_bounds_def, scalar_matches_def, reference_matches_def,
   single_matches_def, values_match_def, default_scalar_def];

val scalar_result_pre_def = cv_trans_pre "scalar_result_pre" scalar_result_def;
Theorem scalar_result_pre[cv_pre]:
  ∀ty mode i. scalar_result_pre ty mode i
Proof
  rw[scalar_result_pre_def]
  \\ intLib.COOPER_TAC
QED

val () = List.app cv_auto_trans
  [trunc_div_def, eval_scalar_operation_def, define_binding_def,
   assign_binding_def, read_memory_def, write_memory_def, write_target_def];
