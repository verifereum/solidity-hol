Theory solidityAST
Ancestors
  arithmetic list
Libs
  cv_transLib

Datatype:
  ast_id = AstId num
End

Datatype:
  data_location
  = StorageLoc
  | MemoryLoc
  | CalldataLoc
End

Datatype:
  address_payability
  = NonpayableAddress
  | PayableAddress
End

Datatype:
  function_kind
  = InternalFn
  | ExternalFn
End

Datatype:
  state_mutability
  = PureMut
  | ViewMut
  | NonpayableMut
  | PayableMut
End

Datatype:
  sol_type
  = BoolT
  | UintT num
  | IntT num
  | AddressT address_payability
  | FixedBytesT num
  | BytesT
  | StringT
  | ArrayT sol_type (num option)
  | MappingT sol_type sol_type
  | StructT ast_id
  | EnumT ast_id
  | ContractT ast_id
  | UserValueT ast_id
  | FunctionT function_kind state_mutability
              (sol_type list) (sol_type list)
  | LocatedT data_location sol_type
End

Definition valid_int_width_def:
  valid_int_width n ⇔ 8 ≤ n ∧ n ≤ 256 ∧ n MOD 8 = 0
End

Definition valid_fixed_bytes_width_def:
  valid_fixed_bytes_width n ⇔ 1 ≤ n ∧ n ≤ 32
End

Definition valid_array_length_def:
  (valid_array_length NONE ⇔ T) ∧
  (valid_array_length (SOME n) ⇔ 0 < n)
End

Definition is_value_type_def:
  (is_value_type BoolT ⇔ T) ∧
  (is_value_type (UintT _) ⇔ T) ∧
  (is_value_type (IntT _) ⇔ T) ∧
  (is_value_type (AddressT _) ⇔ T) ∧
  (is_value_type (FixedBytesT _) ⇔ T) ∧
  (is_value_type (EnumT _) ⇔ T) ∧
  (is_value_type (ContractT _) ⇔ T) ∧
  (is_value_type (UserValueT _) ⇔ T) ∧
  (is_value_type (FunctionT _ _ _ _) ⇔ T) ∧
  (is_value_type _ ⇔ F)
End

Definition is_reference_type_def:
  (is_reference_type BytesT ⇔ T) ∧
  (is_reference_type StringT ⇔ T) ∧
  (is_reference_type (ArrayT _ _) ⇔ T) ∧
  (is_reference_type (MappingT _ _) ⇔ T) ∧
  (is_reference_type (StructT _) ⇔ T) ∧
  (is_reference_type (LocatedT _ ty) ⇔ is_reference_type ty) ∧
  (is_reference_type _ ⇔ F)
End

(* Whether a mapping occurs in the type's own structure, through array
 * elements. Struct fields need the declaration environment and are checked by
 * declared_type_ok in solidityCoreWf; a function type is a value and is not
 * looked through.
 *)
Definition contains_mapping_def:
  (contains_mapping (MappingT _ _) ⇔ T) ∧
  (contains_mapping (ArrayT ty _) ⇔ contains_mapping ty) ∧
  (contains_mapping _ ⇔ F)
End

Definition valid_mapping_key_def:
  (valid_mapping_key BoolT ⇔ T) ∧
  (valid_mapping_key (UintT n) ⇔ valid_int_width n) ∧
  (valid_mapping_key (IntT n) ⇔ valid_int_width n) ∧
  (valid_mapping_key (AddressT _) ⇔ T) ∧
  (valid_mapping_key (FixedBytesT n) ⇔ valid_fixed_bytes_width n) ∧
  (valid_mapping_key (EnumT _) ⇔ T) ∧
  (valid_mapping_key (ContractT _) ⇔ T) ∧
  (valid_mapping_key (UserValueT _) ⇔ T) ∧
  (valid_mapping_key BytesT ⇔ T) ∧
  (valid_mapping_key StringT ⇔ T) ∧
  (valid_mapping_key _ ⇔ F)
End

(*
 * Locations may decorate the outer reference structure, and may occur inside
 * nested function signatures, but may not decorate array elements or mapping
 * components directly. This predicate deliberately treats a function signature
 * as an opaque boundary for that purpose.
 *)
Definition outer_location_free_def:
  (outer_location_free (LocatedT _ _) ⇔ F) ∧
  (outer_location_free (ArrayT ty _) ⇔ outer_location_free ty) ∧
  (outer_location_free (MappingT key value) ⇔
    outer_location_free key ∧ outer_location_free value) ∧
  (outer_location_free _ ⇔ T)
End

Definition location_shape_ok_def:
  (location_shape_ok StorageLoc ty ⇔ is_reference_type ty) ∧
  (location_shape_ok MemoryLoc ty ⇔
    is_reference_type ty ∧ ¬contains_mapping ty) ∧
  (location_shape_ok CalldataLoc ty ⇔
    is_reference_type ty ∧ ¬contains_mapping ty)
End

Definition valid_type_shape_def:
  (valid_type_shape BoolT ⇔ T) ∧
  (valid_type_shape (UintT n) ⇔ valid_int_width n) ∧
  (valid_type_shape (IntT n) ⇔ valid_int_width n) ∧
  (valid_type_shape (AddressT _) ⇔ T) ∧
  (valid_type_shape (FixedBytesT n) ⇔ valid_fixed_bytes_width n) ∧
  (valid_type_shape BytesT ⇔ T) ∧
  (valid_type_shape StringT ⇔ T) ∧
  (valid_type_shape (ArrayT ty length) ⇔
    valid_type_shape ty ∧ outer_location_free ty ∧
    valid_array_length length) ∧
  (valid_type_shape (MappingT key value) ⇔
    valid_mapping_key key ∧ valid_type_shape value ∧
    outer_location_free key ∧ outer_location_free value) ∧
  (valid_type_shape (StructT _) ⇔ T) ∧
  (valid_type_shape (EnumT _) ⇔ T) ∧
  (valid_type_shape (ContractT _) ⇔ T) ∧
  (valid_type_shape (UserValueT _) ⇔ T) ∧
  (valid_type_shape (FunctionT _ _ parameters returns) ⇔
    valid_type_shapes parameters ∧ valid_type_shapes returns) ∧
  (valid_type_shape (LocatedT location ty) ⇔
    valid_type_shape ty ∧ outer_location_free ty ∧
    location_shape_ok location ty) ∧
  (valid_type_shapes [] ⇔ T) ∧
  (valid_type_shapes (ty :: tys) ⇔ valid_type_shape ty ∧ valid_type_shapes tys)
Termination
  WF_REL_TAC ‘measure (λx. case x of
    INL ty => sol_type_size ty
  | INR tys => list_size sol_type_size tys)’ >>
  rw[fetch "-" "sol_type_size_def", list_size_def]
End

val () = cv_auto_trans_rec valid_type_shape_def (
  WF_REL_TAC ‘measure (λx. case x of
    INL ty => cv_size ty
  | INR tys => cv_size tys)’ >> cv_termination_tac
);

Theorem valid_type_shapes_every[simp]:
  valid_type_shapes tys ⇔ EVERY valid_type_shape tys
Proof
  Induct_on ‘tys’ >> simp[valid_type_shape_def]
QED

Theorem valid_uint256:
  valid_type_shape (UintT 256)
Proof
  EVAL_TAC
QED

Theorem invalid_uint7:
  ¬valid_type_shape (UintT 7)
Proof
  EVAL_TAC
QED

Theorem valid_calldata_array:
  valid_type_shape
    (LocatedT CalldataLoc (ArrayT (UintT 256) NONE))
Proof
  SIMP_TAC (srw_ss())
    [valid_type_shape_def, valid_int_width_def, valid_array_length_def,
     outer_location_free_def, location_shape_ok_def, is_reference_type_def,
     contains_mapping_def]
QED

Theorem invalid_located_value:
  ¬valid_type_shape (LocatedT MemoryLoc (UintT 256))
Proof
  EVAL_TAC
QED

Theorem invalid_located_array_element:
  ¬valid_type_shape
    (ArrayT (LocatedT MemoryLoc (ArrayT (UintT 256) NONE)) NONE)
Proof
  EVAL_TAC
QED

Theorem valid_string_key_mapping:
  valid_type_shape (MappingT StringT (UintT 256)) ∧
  valid_type_shape (LocatedT StorageLoc (MappingT StringT (UintT 256)))
Proof
  EVAL_TAC
QED

Theorem valid_bytes_key_mapping:
  valid_type_shape (MappingT BytesT (UintT 256)) ∧
  valid_type_shape (LocatedT StorageLoc (MappingT BytesT (UintT 256)))
Proof
  EVAL_TAC
QED

Theorem invalid_array_key_mapping:
  ¬valid_type_shape (MappingT (ArrayT (UintT 256) NONE) (UintT 256))
Proof
  EVAL_TAC
QED

Theorem invalid_mapping_key_mapping:
  ¬valid_type_shape
    (MappingT (MappingT (UintT 256) (UintT 256)) (UintT 256))
Proof
  EVAL_TAC
QED

Theorem valid_memory_array:
  valid_type_shape (LocatedT MemoryLoc (ArrayT (UintT 256) (SOME 3)))
Proof
  EVAL_TAC
QED

Theorem valid_storage_mapping_array:
  valid_type_shape
    (LocatedT StorageLoc (ArrayT (MappingT (UintT 256) (UintT 256)) NONE)) ∧
  valid_type_shape (LocatedT StorageLoc (MappingT (UintT 256) (UintT 256)))
Proof
  EVAL_TAC
QED

Theorem invalid_memory_mapping_array:
  ¬valid_type_shape
    (LocatedT MemoryLoc (ArrayT (MappingT (UintT 256) (UintT 256)) NONE))
Proof
  EVAL_TAC
QED

Theorem invalid_calldata_nested_mapping_array:
  ¬valid_type_shape
    (LocatedT CalldataLoc
       (ArrayT (ArrayT (MappingT (UintT 256) (UintT 256)) NONE) (SOME 2)))
Proof
  EVAL_TAC
QED
