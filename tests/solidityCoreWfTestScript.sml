(* Positive and negative well-formedness witnesses. *)
Theory solidityCoreWfTest
Ancestors
  solidityCoreWf
Libs
  intLib

Definition u256_def:
  u256 = UintT 256
End

Definition test_decls_def:
  test_decls = [(AstId 900, EnumDeclaration 3)]
End

(* add(x, y) returns (r): r := x + y (checked). *)
Definition add_proc_def:
  add_proc = <|
    procedure_id := AstId 1;
    parameters := [(AstId 10, u256); (AstId 11, u256)];
    return_bindings := [(AstId 12, u256)];
    body := [
      DefineStmt (AstId 13) (SingleType u256)
        (ScalarOperation u256 CheckedArithmetic AddOp
           [BoundAtom (AstId 10); BoundAtom (AstId 11)]);
      ReturnStmt [BoundAtom (AstId 13)]
    ]
  |>
End

(* count(n): effectful condition prelude, capture/write, break/continue. *)
Definition count_proc_def:
  count_proc = <|
    procedure_id := AstId 2;
    parameters := [(AstId 20, u256)];
    return_bindings := [(AstId 21, u256)];
    body := [
      DefineStmt (AstId 22) (SingleType u256)
        (ConvertOperation u256 (ConstantAtom (IntegerValue 0)));
      WhileStmt
        [DefineStmt (AstId 23) (SingleType BoolT)
           (ScalarOperation u256 UncheckedArithmetic LessThanOp
              [BoundAtom (AstId 22); BoundAtom (AstId 20)])]
        (BoundAtom (AstId 23))
        [DefineStmt (AstId 24) (SingleType u256)
           (ScalarOperation u256 CheckedArithmetic AddOp
              [BoundAtom (AstId 22); ConstantAtom (IntegerValue 1)]);
         CaptureBindingStmt (AstId 25) (AstId 22);
         WriteScalarStmt (AstId 25) u256 (BoundAtom (AstId 24));
         DefineStmt (AstId 26) (SingleType BoolT)
           (ScalarOperation u256 UncheckedArithmetic EqualOp
              [BoundAtom (AstId 24); ConstantAtom (IntegerValue 10)]);
         IfStmt (BoundAtom (AstId 26)) [BreakStmt] [ContinueStmt]];
      ReturnStmt [BoundAtom (AstId 22)]
    ]
  |>
End

(* pair() returns (uint256, bool). *)
Definition pair_proc_def:
  pair_proc = <|
    procedure_id := AstId 3;
    parameters := [];
    return_bindings := [(AstId 30, u256); (AstId 31, BoolT)];
    body := [ReturnStmt [ConstantAtom (IntegerValue 7);
                         ConstantAtom (BoolValue T)]]
  |>
End

(* first(): destructure a multiple-return call; enum constant in range. *)
Definition first_proc_def:
  first_proc = <|
    procedure_id := AstId 4;
    parameters := [];
    return_bindings := [(AstId 40, u256)];
    body := [
      DefineStmt (AstId 41) (ProductType [SingleType u256; SingleType BoolT])
        (InternalCallOperation (AstId 3) []);
      DefineStmt (AstId 42) (SingleType u256)
        (TupleComponentOperation 0 (BoundAtom (AstId 41)));
      DefineStmt (AstId 43) (SingleType (EnumT (AstId 900)))
        (ConvertOperation (EnumT (AstId 900)) (ConstantAtom (IntegerValue 2)));
      ReturnStmt [BoundAtom (AstId 42)]
    ]
  |>
End

(* fact(n): recursive internal call. *)
Definition fact_proc_def:
  fact_proc = <|
    procedure_id := AstId 5;
    parameters := [(AstId 50, u256)];
    return_bindings := [(AstId 51, u256)];
    body := [
      DefineStmt (AstId 52) (SingleType BoolT)
        (ScalarOperation u256 UncheckedArithmetic EqualOp
           [BoundAtom (AstId 50); ConstantAtom (IntegerValue 0)]);
      IfStmt (BoundAtom (AstId 52))
        [ReturnStmt [ConstantAtom (IntegerValue 1)]]
        [DefineStmt (AstId 53) (SingleType u256)
           (ScalarOperation u256 CheckedArithmetic SubtractOp
              [BoundAtom (AstId 50); ConstantAtom (IntegerValue 1)]);
         DefineStmt (AstId 54) (SingleType u256)
           (InternalCallOperation (AstId 5) [BoundAtom (AstId 53)]);
         DefineStmt (AstId 55) (SingleType u256)
           (ScalarOperation u256 CheckedArithmetic MultiplyOp
              [BoundAtom (AstId 50); BoundAtom (AstId 54)]);
         ReturnStmt [BoundAtom (AstId 55)]]
    ]
  |>
End

(* Modifier-style wrapper: placeholder call, write own return binding,
 * postlude void call, then `return;` lowered to the return bindings.
 *)
Definition wrapper_proc_def:
  wrapper_proc = <|
    procedure_id := AstId 6;
    parameters := [];
    return_bindings := [(AstId 60, u256)];
    body := [
      DefineStmt (AstId 61) (SingleType u256)
        (InternalCallOperation (AstId 1)
           [ConstantAtom (IntegerValue 1); ConstantAtom (IntegerValue 2)]);
      CaptureBindingStmt (AstId 62) (AstId 60);
      WriteScalarStmt (AstId 62) u256 (BoundAtom (AstId 61));
      DefineStmt (AstId 63) (ProductType []) (InternalCallOperation (AstId 7) []);
      ReturnStmt [BoundAtom (AstId 60)]
    ]
  |>
End

Definition void_proc_def:
  void_proc = <|
    procedure_id := AstId 7;
    parameters := [];
    return_bindings := [];
    body := [RevertStmt (ConstantAtom (BytesValue []))]
  |>
End

Definition test_program_def:
  test_program = <|
    procedures := [add_proc; count_proc; pair_proc; first_proc; fact_proc;
                   wrapper_proc; void_proc];
    entry_procedure := AstId 6
  |>
End

Definition test_env_def:
  test_env = core_program_environment test_decls test_program
End

Theorem test_program_wf:
  wf_core_program test_env test_program
Proof
  EVAL_TAC
QED

(* Negative witnesses: each replaces one procedure body with a single defect. *)

Definition with_body_def:
  with_body body = <|
    procedure_id := AstId 8;
    parameters := [(AstId 80, u256)];
    return_bindings := [(AstId 81, u256)];
    body := body
  |>
End

Theorem unbound_atom_rejected:
  ¬wf_core_procedure test_env (with_body [ReturnStmt [BoundAtom (AstId 99)]])
Proof
  EVAL_TAC
QED

Theorem out_of_range_constant_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType (UintT 8))
       (ConvertOperation (UintT 8) (ConstantAtom (IntegerValue 300)))])
Proof
  EVAL_TAC
QED

Theorem enum_constant_out_of_range_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType (EnumT (AstId 900)))
       (ConvertOperation (EnumT (AstId 900)) (ConstantAtom (IntegerValue 3)))])
Proof
  EVAL_TAC
QED

Theorem call_arity_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType u256)
       (InternalCallOperation (AstId 1) [BoundAtom (AstId 80)])])
Proof
  EVAL_TAC
QED

Theorem unknown_procedure_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType u256)
       (InternalCallOperation (AstId 77) [])])
Proof
  EVAL_TAC
QED

Theorem call_result_shape_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType u256)
       (InternalCallOperation (AstId 3) [])])
Proof
  EVAL_TAC
QED

Theorem return_arity_rejected:
  ¬wf_core_procedure test_env (with_body [ReturnStmt []])
Proof
  EVAL_TAC
QED

Theorem break_outside_loop_rejected:
  ¬wf_core_procedure test_env (with_body [BreakStmt])
Proof
  EVAL_TAC
QED

Theorem break_in_prelude_rejected:
  ¬wf_core_procedure test_env (with_body [
     WhileStmt [BreakStmt] (ConstantAtom (BoolValue T)) []])
Proof
  EVAL_TAC
QED

Theorem continue_outside_loop_rejected:
  ¬wf_core_procedure test_env (with_body [ContinueStmt])
Proof
  EVAL_TAC
QED

Theorem branch_local_escape_rejected:
  ¬wf_core_procedure test_env (with_body [
     IfStmt (ConstantAtom (BoolValue T))
       [DefineStmt (AstId 82) (SingleType u256)
          (ConvertOperation u256 (ConstantAtom (IntegerValue 1)))] [];
     ReturnStmt [BoundAtom (AstId 82)]])
Proof
  EVAL_TAC
QED

Theorem singleton_product_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (ProductType [SingleType u256])
       (TupleOperation [BoundAtom (AstId 80)])])
Proof
  EVAL_TAC
QED

Theorem comparison_annotation_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType u256)
       (ScalarOperation u256 UncheckedArithmetic EqualOp
          [BoundAtom (AstId 80); BoundAtom (AstId 80)])])
Proof
  EVAL_TAC
QED

Theorem shadowing_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 80) (SingleType u256)
       (ConvertOperation u256 (ConstantAtom (IntegerValue 1)))])
Proof
  EVAL_TAC
QED

Theorem write_without_capture_rejected:
  ¬wf_core_procedure test_env (with_body [
     WriteScalarStmt (AstId 81) u256 (BoundAtom (AstId 80))])
Proof
  EVAL_TAC
QED

Theorem reference_operation_rejected:
  ¬wf_core_procedure test_env (with_body [
     DefineStmt (AstId 82) (SingleType u256)
       (ReadOperation u256 (BoundAtom (AstId 80)))])
Proof
  EVAL_TAC
QED

Theorem duplicate_procedure_rejected:
  ¬wf_core_program
     (core_program_environment test_decls
        (test_program with procedures := add_proc :: test_program.procedures))
     (test_program with procedures := add_proc :: test_program.procedures)
Proof
  EVAL_TAC
QED

Theorem missing_entry_rejected:
  ¬wf_core_program test_env (test_program with entry_procedure := AstId 77)
Proof
  EVAL_TAC
QED