(* Hand-written core witnesses, not imported or compiled Solidity fixtures. *)
Theory solidityInterpreterTest
Ancestors
  solidityInterpreter solidityValue solidityState vfmState finite_map
Libs
  cv_transLib wordsLib

Definition interpreter_initial_def:
  interpreter_initial = <|
    world := <| accounts := empty_accounts; transient := empty_transient_storage; logs := [] |>;
    frame := <| self_address := 0x1001w; code_address := 0x1001w;
      sender_address := 0x1000w; call_value := 0; call_data := []; static_context := F |>;
    scopes := [FEMPTY]; heap := FEMPTY; next_heap_id := 0; targets := FEMPTY |>
End

Definition integer_atom_def:
  integer_atom n = ConstantAtom (IntegerValue (&n))
End

Definition integer_definition_def:
  integer_definition id n = DefineStmt (AstId id) (SingleType (UintT 8))
    (ConvertOperation (UintT 8) (integer_atom n))
End

Definition increment_binding_def:
  increment_binding id temporary target =
    [DefineStmt (AstId temporary) (SingleType (UintT 8))
       (ScalarOperation (UintT 8) CheckedArithmetic AddOp
         [BoundAtom (AstId id); integer_atom 1]);
     CaptureBindingStmt (AstId target) (AstId id);
     WriteScalarStmt (AstId target) (UintT 8) (BoundAtom (AstId temporary))]
End

Definition loop_program_def:
  loop_program = <| procedures := []; entry_procedure := AstId 0 |>
End

Definition counting_loop_def:
  counting_loop = WhileStmt
    [DefineStmt (AstId 2) (SingleType BoolT)
       (ScalarOperation (UintT 8) CheckedArithmetic LessThanOp
         [BoundAtom (AstId 1); integer_atom 3])]
    (BoundAtom (AstId 2))
    (increment_binding 1 3 4 ++ [ContinueStmt; RevertStmt (ConstantAtom (BytesValue [99w]))])
End

Definition block_summary_def:
  block_summary fuel statements =
    let result = eval_block fuel loop_program statements interpreter_initial [GasLeftObservation 17] in
    (result.completion,
     OPTION_MAP (λbinding. binding.binding_value) (lookup_binding (AstId 1) result.state.scopes),
     LENGTH result.state.scopes, result.unused_gas_evidence)
End

Definition fresh_body_def:
  fresh_body = <| procedure_id := AstId 10; parameters := [];
    return_bindings := [(AstId 1, UintT 8)];
    body := increment_binding 1 3 4 ++ [ReturnStmt []; RevertStmt (ConstantAtom (BytesValue [99w]))] |>
End

Definition wrapper_call_def:
  wrapper_call tuple_id value_id =
    [DefineStmt (AstId tuple_id) (ProductType [SingleType (UintT 8)])
       (InternalCallOperation (AstId 10) []);
     DefineStmt (AstId value_id) (SingleType (UintT 8))
       (TupleComponentOperation 0 (BoundAtom (AstId tuple_id)));
     CaptureBindingStmt (AstId 4) (AstId 1);
     WriteScalarStmt (AstId 4) (UintT 8) (BoundAtom (AstId value_id))]
End

Definition modifier_wrapper_def:
  modifier_wrapper = <| procedure_id := AstId 11; parameters := [];
    return_bindings := [(AstId 1, UintT 8)];
    body := wrapper_call 5 6 ++ wrapper_call 7 8 ++
      increment_binding 1 9 4 ++ [ReturnStmt []] |>
End

Definition recursive_body_def:
  recursive_body = <| procedure_id := AstId 12;
    parameters := [(AstId 20, UintT 8)]; return_bindings := [(AstId 21, UintT 8)];
    body := [
      DefineStmt (AstId 22) (SingleType BoolT)
        (ScalarOperation (UintT 8) CheckedArithmetic EqualOp
          [BoundAtom (AstId 20); integer_atom 0]);
      IfStmt (BoundAtom (AstId 22)) [ReturnStmt [integer_atom 0]] [];
      DefineStmt (AstId 23) (SingleType (UintT 8))
        (ScalarOperation (UintT 8) CheckedArithmetic SubtractOp
          [BoundAtom (AstId 20); integer_atom 1]);
      DefineStmt (AstId 24) (ProductType [SingleType (UintT 8)])
        (InternalCallOperation (AstId 12) [BoundAtom (AstId 23)]);
      DefineStmt (AstId 25) (SingleType (UintT 8))
        (TupleComponentOperation 0 (BoundAtom (AstId 24)));
      DefineStmt (AstId 26) (SingleType (UintT 8))
        (ScalarOperation (UintT 8) CheckedArithmetic AddOp
          [BoundAtom (AstId 25); integer_atom 1]);
      ReturnStmt [BoundAtom (AstId 26)]] |>
End

Definition interpreter_program_def:
  interpreter_program = <| procedures := [fresh_body; modifier_wrapper; recursive_body];
    entry_procedure := AstId 11 |>
End

Definition invocation_summary_def:
  invocation_summary fuel program id arguments =
    let result = invoke_source fuel program id arguments interpreter_initial [CallGasObservation 22] in
    (result.completion, result.state.scopes = interpreter_initial.scopes,
     result.state.targets = interpreter_initial.targets, result.unused_gas_evidence)
End

val () = List.app cv_auto_trans
  [interpreter_initial_def, integer_atom_def, integer_definition_def,
   increment_binding_def, loop_program_def, counting_loop_def, block_summary_def,
   fresh_body_def, wrapper_call_def, modifier_wrapper_def, recursive_body_def,
   interpreter_program_def, invocation_summary_def];

Theorem zero_fuel_runs_finite_siblings:
  block_summary 0 [integer_definition 1 10; integer_definition 2 20;
    DefineStmt (AstId 3) (SingleType (UintT 8))
      (ScalarOperation (UintT 8) CheckedArithmetic AddOp
        [BoundAtom (AstId 1); BoundAtom (AstId 2)]);
    ReturnStmt [BoundAtom (AstId 3)]] =
    (ReturnCompletion [ScalarValue (IntegerValue 30)],
     SOME (ScalarValue (IntegerValue 10)), 1, [GasLeftObservation 17])
Proof
  CONV_TAC cv_eval
QED

Theorem condition_repeats_and_continue_skips_suffix:
  block_summary 3 [integer_definition 1 0; counting_loop; ReturnStmt [BoundAtom (AstId 1)]] =
    (ReturnCompletion [ScalarValue (IntegerValue 3)],
     SOME (ScalarValue (IntegerValue 3)), 1, [GasLeftObservation 17])
Proof
  CONV_TAC cv_eval
QED

Theorem insufficient_loop_depth_is_not_revert:
  block_summary 2 [integer_definition 1 0; counting_loop] =
    (FuelExhausted, SOME (ScalarValue (IntegerValue 3)), 1, [GasLeftObservation 17])
Proof
  CONV_TAC cv_eval
QED

Theorem false_loop_needs_no_fuel:
  block_summary 0 [WhileStmt [] (ConstantAtom (BoolValue F)) [RevertStmt (integer_atom 0)]] =
    (NormalCompletion, NONE, 1, [GasLeftObservation 17])
Proof
  CONV_TAC cv_eval
QED

Theorem break_stops_loop_without_repeating:
  block_summary 0 [WhileStmt [] (ConstantAtom (BoolValue T))
    [BreakStmt; RevertStmt (integer_atom 0)]] =
    (NormalCompletion, NONE, 1, [GasLeftObservation 17])
Proof
  CONV_TAC cv_eval
QED

Theorem returning_body_needs_no_loop_fuel:
  block_summary 0 [WhileStmt [] (ConstantAtom (BoolValue T)) [ReturnStmt [integer_atom 7]]] =
    (ReturnCompletion [ScalarValue (IntegerValue 7)], NONE, 1, [GasLeftObservation 17])
Proof
  CONV_TAC cv_eval
QED

Theorem invalid_loop_condition_is_explicit:
  block_summary 0 [WhileStmt [] (BoundAtom (AstId 999)) []] =
    (InvalidCompletion "boolean loop condition required", NONE, 1, [GasLeftObservation 17])
Proof
  CONV_TAC cv_eval
QED

Theorem checked_overflow_panics:
  eval_scalar_operation (UintT 8) CheckedArithmetic AddOp
    [ScalarValue (IntegerValue 255); ScalarValue (IntegerValue 1)] = INL (PanicCompletion 17)
Proof
  CONV_TAC cv_eval
QED

Theorem unchecked_arithmetic_wraps:
  eval_scalar_operation (UintT 8) UncheckedArithmetic AddOp
    [ScalarValue (IntegerValue 255); ScalarValue (IntegerValue 1)] = INR (ScalarValue (IntegerValue 0))
Proof
  CONV_TAC cv_eval
QED

Theorem signed_division_and_remainder_truncate_to_zero:
  eval_scalar_operation (IntT 8) CheckedArithmetic DivideOp
    [ScalarValue (IntegerValue (-7)); ScalarValue (IntegerValue 3)] =
      INR (ScalarValue (IntegerValue (-2))) ∧
  eval_scalar_operation (IntT 8) CheckedArithmetic RemainderOp
    [ScalarValue (IntegerValue (-7)); ScalarValue (IntegerValue 3)] =
      INR (ScalarValue (IntegerValue (-1)))
Proof
  CONV_TAC cv_eval
QED

Theorem unchecked_division_by_zero_still_panics:
  eval_scalar_operation (UintT 8) UncheckedArithmetic DivideOp
    [ScalarValue (IntegerValue 1); ScalarValue (IntegerValue 0)] = INL (PanicCompletion 18)
Proof
  CONV_TAC cv_eval
QED

Theorem explicit_integer_conversion_wraps:
  pure_operation (ConvertOperation (UintT 8) (integer_atom 300)) interpreter_initial =
    INR (ScalarValue (IntegerValue 44))
Proof
  CONV_TAC cv_eval
QED

Theorem modifier_repeated_body_has_fresh_returns_and_postlude:
  invocation_summary 2 interpreter_program (AstId 11) [] =
    (ReturnCompletion [ScalarValue (IntegerValue 2)], T, T, [CallGasObservation 22])
Proof
  CONV_TAC cv_eval
QED

Theorem recursive_invocations_are_isolated:
  invocation_summary 4 interpreter_program (AstId 12) [ScalarValue (IntegerValue 3)] =
    (ReturnCompletion [ScalarValue (IntegerValue 3)], T, T, [CallGasObservation 22])
Proof
  CONV_TAC cv_eval
QED

Theorem recursive_fuel_exhaustion_restores_caller:
  invocation_summary 3 interpreter_program (AstId 12) [ScalarValue (IntegerValue 3)] =
    (FuelExhausted, T, T, [CallGasObservation 22])
Proof
  CONV_TAC cv_eval
QED

Theorem excessive_fuel_does_not_change_recursive_witness:
  invocation_summary 10 interpreter_program (AstId 12) [ScalarValue (IntegerValue 3)] =
  invocation_summary 4 interpreter_program (AstId 12) [ScalarValue (IntegerValue 3)]
Proof
  CONV_TAC cv_eval
QED

Theorem external_calls_are_not_mocked:
  (eval_core 10 interpreter_program
    (RunOperation (ExternalCallOperation ExternalCall [])) interpreter_initial []).completion =
    InvalidCompletion "unsupported operation"
Proof
  CONV_TAC cv_eval
QED

Theorem reverting_body_skips_modifier_postlude:
  invocation_summary 2
    (interpreter_program with procedures :=
      [fresh_body with body := [RevertStmt (ConstantAtom (BytesValue [7w]))]; modifier_wrapper])
    (AstId 11) [] = (RevertCompletion [7w], T, T, [CallGasObservation 22])
Proof
  CONV_TAC cv_eval
QED

Theorem panicking_body_skips_modifier_postlude:
  invocation_summary 2
    (interpreter_program with procedures :=
      [fresh_body with body := [DefineStmt (AstId 30) (SingleType (UintT 8))
        (ScalarOperation (UintT 8) CheckedArithmetic AddOp [integer_atom 255; integer_atom 1])];
       modifier_wrapper])
    (AstId 11) [] = (PanicCompletion 17, T, T, [CallGasObservation 22])
Proof
  CONV_TAC cv_eval
QED

Theorem named_return_defaults_are_zero:
  invocation_summary 1 (interpreter_program with procedures := [fresh_body with body := []])
    (AstId 10) [] = (ReturnCompletion [ScalarValue (IntegerValue 0)], T, T, [CallGasObservation 22])
Proof
  CONV_TAC cv_eval
QED

Theorem tuple_projection_out_of_bounds_is_invalid:
  block_summary 0
    [DefineStmt (AstId 1) (ProductType []) (TupleOperation []);
     DefineStmt (AstId 2) (SingleType (UintT 8))
       (TupleComponentOperation 0 (BoundAtom (AstId 1)))] =
    (InvalidCompletion "tuple component out of bounds", SOME (TupleValue []), 1, [GasLeftObservation 17])
Proof
  CONV_TAC cv_eval
QED

Theorem duplicate_procedures_are_invalid:
  invocation_summary 1 (interpreter_program with procedures := [fresh_body; fresh_body])
    (AstId 10) [] =
    (InvalidCompletion "missing or duplicate procedure", T, T, [CallGasObservation 22])
Proof
  CONV_TAC cv_eval
QED

Definition reference_alias_summary_def:
  reference_alias_summary =
    let ty = LocatedT MemoryLoc (ArrayT (UintT 8) NONE) in
    let a = MemoryReference (HeapId 0) 0 (ArrayT (UintT 8) NONE) in
    let b = MemoryReference (HeapId 1) 0 (ArrayT (UintT 8) NONE) in
    case initialise_parameters [(AstId 1, ty); (AstId 2, ty)]
      [ReferenceValue a; ReferenceValue b]
      (interpreter_initial with heap := FEMPTY |+
        (0, <| object_type := ArrayT (UintT 8) NONE; object_length := 1;
          object_cells := FEMPTY |+ (0, ScalarValue (IntegerValue 1)) |>) |+
        (1, <| object_type := ArrayT (UintT 8) NONE; object_length := 1;
          object_cells := FEMPTY |+ (0, ScalarValue (IntegerValue 2)) |>)) of
      NONE => NONE
    | SOME entered =>
        let result = eval_block 0 loop_program
          [CaptureValueStmt (AstId 7) (BoundAtom (AstId 1));
           CaptureBindingStmt (AstId 8) (AstId 1);
           BindReferenceStmt (AstId 8) ty (BoundAtom (AstId 2))] entered [] in
        SOME (result.completion,
          eval_atom (BoundAtom (AstId 1)) result.state = SOME (ReferenceValue b),
          FLOOKUP result.state.targets 7 = SOME (ValueTarget a),
          result.state.heap = entered.heap)
End

val () = cv_auto_trans reference_alias_summary_def;

Theorem reference_rebinding_retains_captured_location_without_copy:
  reference_alias_summary = SOME (NormalCompletion, T, T, T)
Proof
  CONV_TAC cv_eval
QED

Theorem selected_entry_executes_wrapper:
  (run_source 2 interpreter_program [] interpreter_initial []).completion =
    ReturnCompletion [ScalarValue (IntegerValue 2)]
Proof
  CONV_TAC cv_eval
QED

Theorem signed_minimum_division_checks_or_wraps:
  eval_scalar_operation (IntT 8) CheckedArithmetic DivideOp
    [ScalarValue (IntegerValue (-128)); ScalarValue (IntegerValue (-1))] =
      INL (PanicCompletion 17) ∧
  eval_scalar_operation (IntT 8) UncheckedArithmetic DivideOp
    [ScalarValue (IntegerValue (-128)); ScalarValue (IntegerValue (-1))] =
      INR (ScalarValue (IntegerValue (-128))) ∧
  eval_scalar_operation (IntT 8) CheckedArithmetic RemainderOp
    [ScalarValue (IntegerValue (-128)); ScalarValue (IntegerValue (-1))] =
      INR (ScalarValue (IntegerValue 0))
Proof
  CONV_TAC cv_eval
QED

Theorem invalid_call_arity_and_return_shape_are_rejected:
  invocation_summary 5 interpreter_program (AstId 12) [] =
    (InvalidCompletion "invalid procedure arguments", T, T, [CallGasObservation 22]) ∧
  invocation_summary 5
    (interpreter_program with procedures :=
      [fresh_body with body := [ReturnStmt [integer_atom 0; integer_atom 1]]]) (AstId 10) [] =
    (InvalidCompletion "return type mismatch", T, T, [CallGasObservation 22])
Proof
  CONV_TAC cv_eval
QED
