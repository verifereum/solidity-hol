(* Architecture blueprint, not yet an admitted/executable Solidity subset.
 * All effectful child evaluations are ordered by elaboration into core blocks.
 *)
Theory solidityCore
Ancestors
  solidityAST vfmContext

Datatype:
  layout_id = LayoutId num
End

Datatype:
  heap_id = HeapId num
End

Datatype:
  storage_backend = PersistentStorage | TransientStorage
End

(* Captured locations, never source paths to reevaluate. Layout IDs resolve in
 * an imported layout environment; validity is a future environment predicate.
 *)
Datatype:
  reference
  = StorageReference storage_backend address bytes32 num sol_type layout_id
  | MemoryReference heap_id num sol_type
  | CalldataReference num num sol_type
End

Datatype:
  scalar
  = BoolValue bool
  | IntegerValue int
  | AddressValue address
  | BytesValue (byte list)
  | InternalFunctionValue ast_id
  | ExternalFunctionValue address (byte list)
End

Datatype:
  runtime_value
  = ScalarValue scalar
  | ReferenceValue reference
  | TupleValue (runtime_value list)
End

(* Operands are pure: effects and intermediate results have already been named.
 * Types belong to operations/bindings, not integer payloads.
 *)
Datatype:
  core_value_type = SingleType sol_type | ProductType (core_value_type list)
End

Datatype:
  core_atom = BoundAtom ast_id | ConstantAtom scalar
End

Datatype:
  arithmetic_mode = CheckedArithmetic | UncheckedArithmetic
End

Datatype:
  core_operator
  = AddOp | SubtractOp | MultiplyOp | DivideOp | RemainderOp
  | EqualOp | LessThanOp | BitAndOp | BitOrOp | BitXorOp
End

Datatype:
  navigation = FieldNavigation ast_id | IndexNavigation core_atom
End

(* BindTarget includes local variables and temporaries. ReferenceFieldTarget
 * supports rebinding a reference-valued memory member, not storage copying.
 *)
Datatype:
  captured_target
  = BindTarget ast_id
  | ValueTarget reference
  | ReferenceFieldTarget heap_id num sol_type
End

Datatype:
  external_kind = ExternalCall | ExternalStaticCall | ExternalDelegateCall
End

Datatype:
  core_operation
  = ScalarOperation sol_type arithmetic_mode core_operator (core_atom list)
  | ConvertOperation sol_type core_atom
  | TupleOperation (core_atom list)
  | TupleComponentOperation num core_atom
  | ReadOperation sol_type core_atom
  | NavigateOperation sol_type core_atom navigation
  | InternalCallOperation ast_id (core_atom list)
  | ExternalCallOperation external_kind (core_atom list)
End

(* Explicitly separate scalar writes, reference binding, and content copying.
 * Copy traversal is independently terminating, not fuel-indexed.
 * While/internal recursion need depth fuel; finite syntax/list traversal does not.
 *)
Datatype:
  core_stmt
  = DefineStmt ast_id core_value_type core_operation
  | CaptureBindingStmt ast_id ast_id
  | CaptureValueStmt ast_id core_atom
  | CaptureReferenceFieldStmt ast_id core_atom navigation
  | WriteScalarStmt ast_id sol_type core_atom
  | BindReferenceStmt ast_id sol_type core_atom
  | CopyContentsStmt sol_type sol_type core_atom core_atom
  | IfStmt core_atom (core_stmt list) (core_stmt list)
  | WhileStmt (core_stmt list) core_atom (core_stmt list)
  | ReturnStmt (core_atom list)
  | BreakStmt
  | ContinueStmt
  | RevertStmt core_atom
End

Datatype:
  core_procedure = <|
    procedure_id : ast_id;
    parameters : (ast_id # sol_type) list;
    return_bindings : (ast_id # sol_type) list;
    body : core_stmt list
  |>
End

Datatype:
  core_program = <|
    procedures : core_procedure list;
    entry_procedure : ast_id
  |>
End

(* Distinct completions: return is caught by procedure/wrapper invocation;
 * break/continue by loops. Errors/resources must not masquerade as reverts.
 *)
Datatype:
  source_completion
  = NormalCompletion
  | ReturnCompletion (runtime_value list)
  | BreakCompletion
  | ContinueCompletion
  | RevertCompletion (byte list)
  | PanicCompletion num
  | InvalidCompletion string
  | FuelExhausted
End

Definition is_abrupt_def:
  is_abrupt completion ⇔ completion ≠ NormalCompletion
End

Theorem fuel_is_not_revert:
  FuelExhausted ≠ RevertCompletion data
Proof
  simp[]
QED

Theorem reference_binding_is_not_copying:
  BindReferenceStmt target ty value ≠ CopyContentsStmt src_ty dst_ty src dst
Proof
  simp[]
QED
