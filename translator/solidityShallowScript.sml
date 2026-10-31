(* The target of the core-to-HOL translator (solidityTranslateLib):
 * shallow functions over native HOL values, their result type, and the lemmas
 * its correspondence proofs use.
 *
 * A translated procedure f gets a theorem
 *   pre args ⇒ ∃fuel. ∀m st gas. fuel ≤ m ⇒
 *     invoke_source m env f_id (encoded args) st gas =
 *       <| completion := result_completion enc (f args); state := st;
 *          unused_gas_evidence := gas |>
 * Values: uintN is num and bool is bool. A failed arithmetic check is Panics;
 * Reverts is not produced yet (docs/translator.md lists what is not covered).
 * Return, break and continue are control flow in the shallow terms.
 *)
Theory solidityShallow
Ancestors
  arithmetic integer finite_map solidityAST solidityCore solidityCoreWf solidityScalar solidityState
  solidityEvaluator solidityEvaluatorProps
Libs
  intLib

Datatype:
  sol_result = Returns 'a | Reverts (byte list) | Panics num
End

Definition sol_bind_def:
  sol_bind m f =
    case m of
      Returns x => f x
    | Reverts bs => Reverts bs
    | Panics c => Panics c
End

Theorem sol_bind_cong[defncong]:
  m1 = m2 ∧ (∀x. m2 = Returns x ⇒ f1 x = f2 x) ⇒
  sol_bind m1 f1 = sol_bind m2 f2
Proof
  Cases_on ‘m2’ >> rw[sol_bind_def]
QED

(* Checked unsigned arithmetic *)

Definition uint_add_def:
  uint_add n (x : num) y =
    if x + y < 2 ** n then Returns (x + y) else Panics panic_arithmetic
End

Definition uint_sub_def:
  uint_sub (x : num) y = if y ≤ x then Returns (x - y) else Panics panic_arithmetic
End

Definition uint_mul_def:
  uint_mul n (x : num) y =
    if x * y < 2 ** n then Returns (x * y) else Panics panic_arithmetic
End

Definition uint_div_def:
  uint_div (x : num) y =
    if y = 0 then Panics panic_division_by_zero else Returns (x DIV y)
End

Definition uint_mod_def:
  uint_mod (x : num) y =
    if y = 0 then Panics panic_division_by_zero else Returns (x MOD y)
End

(* Encodings *)

Definition uint_value_def:
  uint_value (x : num) = ScalarValue (IntegerValue (&x))
End

Definition bool_value_def:
  bool_value b = ScalarValue (BoolValue b)
End

Definition result_completion_def:
  result_completion enc r =
    case r of
      Returns v => ReturnCompletion (enc v)
    | Reverts bs => RevertCompletion bs
    | Panics c => PanicCompletion c
End

Definition result_outcome_def:
  result_outcome enc r =
    case r of
      Returns v => ValueOk (enc v)
    | Reverts bs => ValueAbrupt (RevertCompletion bs)
    | Panics c => ValueAbrupt (PanicCompletion c)
End

(* Operations on in-range operands *)

Theorem uint_in_range[local]:
  integer_in_range F n (&x) ⇔ x < 2 ** n
Proof
  simp[integer_in_range_def]
QED

Theorem uint_typed[local]:
  scalar_has_type env (UintT n) (IntegerValue (&x)) ⇔ x < 2 ** n
Proof
  simp[scalar_has_type_def, elementary_scalar_has_type_def, uint_in_range]
QED

Theorem uint_binary_signature[local]:
  op ∈ {AddOp; SubtractOp; MultiplyOp; DivideOp; RemainderOp} ⇒
  scalar_operator_signature op (UintT n) = SOME ([UintT n; UintT n], UintT n)
Proof
  rw[scalar_operator_signature_def] >> simp[]
QED

Theorem uint_arithmetic[local]:
  op ∈ {AddOp; SubtractOp; MultiplyOp; DivideOp; RemainderOp} ∧
  valid_int_width n ∧ x < 2 ** n ∧ y < 2 ** n ⇒
  eval_scalar_operation env (UintT n) mode op
    [IntegerValue (&x); IntegerValue (&y)] =
  eval_integer_operation mode F n op [IntegerValue (&x); IntegerValue (&y)]
Proof
  strip_tac >> drule uint_binary_signature >>
  simp[eval_scalar_operation_def, scalars_have_types_def, uint_typed] >>
  gvs[]
QED

Theorem uint_add_op:
  valid_int_width n ∧ x < 2 ** n ∧ y < 2 ** n ⇒
  scalar_outcome_value
    (eval_scalar_operation env (UintT n) CheckedArithmetic AddOp
       [IntegerValue (&x); IntegerValue (&y)]) =
  result_outcome uint_value (uint_add n x y)
Proof
  strip_tac >> simp[uint_arithmetic] >>
  rw[eval_integer_operation_def, arithmetic_result_def, uint_add_def,
     uint_in_range, result_outcome_def, scalar_outcome_value_def,
     uint_value_def, panic_arithmetic_def, INT_ADD]
QED

Theorem uint_sub_op:
  valid_int_width n ∧ x < 2 ** n ∧ y < 2 ** n ⇒
  scalar_outcome_value
    (eval_scalar_operation env (UintT n) CheckedArithmetic SubtractOp
       [IntegerValue (&x); IntegerValue (&y)]) =
  result_outcome uint_value (uint_sub x y)
Proof
  strip_tac >> simp[uint_arithmetic] >>
  rw[eval_integer_operation_def, arithmetic_result_def, uint_sub_def,
     integer_in_range_def, result_outcome_def, scalar_outcome_value_def,
     uint_value_def, panic_arithmetic_def, INT_SUB] >>
  intLib.ARITH_TAC
QED

Theorem uint_mul_op:
  valid_int_width n ∧ x < 2 ** n ∧ y < 2 ** n ⇒
  scalar_outcome_value
    (eval_scalar_operation env (UintT n) CheckedArithmetic MultiplyOp
       [IntegerValue (&x); IntegerValue (&y)]) =
  result_outcome uint_value (uint_mul n x y)
Proof
  strip_tac >> simp[uint_arithmetic] >>
  rw[eval_integer_operation_def, arithmetic_result_def, uint_mul_def,
     uint_in_range, result_outcome_def, scalar_outcome_value_def,
     uint_value_def, panic_arithmetic_def, INT_MUL]
QED

Theorem uint_div_op:
  valid_int_width n ∧ x < 2 ** n ∧ y < 2 ** n ⇒
  scalar_outcome_value
    (eval_scalar_operation env (UintT n) mode DivideOp
       [IntegerValue (&x); IntegerValue (&y)]) =
  result_outcome uint_value (uint_div x y)
Proof
  strip_tac >> simp[uint_arithmetic] >>
  rw[eval_integer_operation_def, arithmetic_result_def, uint_div_def,
     uint_in_range, result_outcome_def, scalar_outcome_value_def,
     uint_value_def, panic_division_by_zero_def, truncating_quot_def] >>
  ‘x DIV y ≤ x’ by (irule DIV_LESS_EQ >> simp[]) >>
  ‘x DIV y < 2 ** n’ by decide_tac >> gvs[]
QED

Theorem uint_mod_op:
  valid_int_width n ∧ x < 2 ** n ∧ y < 2 ** n ⇒
  scalar_outcome_value
    (eval_scalar_operation env (UintT n) mode RemainderOp
       [IntegerValue (&x); IntegerValue (&y)]) =
  result_outcome uint_value (uint_mod x y)
Proof
  strip_tac >> simp[uint_arithmetic] >>
  rw[eval_integer_operation_def, integer_result_def, uint_mod_def,
     result_outcome_def, scalar_outcome_value_def, uint_value_def,
     panic_division_by_zero_def, truncating_rem_def, truncating_quot_def] >>
  ‘&x − &(y * (x DIV y)) = &(x MOD y) : int’
    by (‘0 < y’ by simp[] >> drule DIVISION >>
        disch_then (qspec_then ‘x’ strip_assume_tac) >>
        ‘y * (x DIV y) ≤ x’ by simp[] >>
        simp[INT_SUB] >> decide_tac) >>
  simp[] >> irule wrap_integer_id >> gvs[valid_int_width_def, uint_in_range] >>
  ‘x MOD y ≤ x’ by simp[MOD_LESS_EQ] >> decide_tac
QED

Theorem uint_less_op:
  valid_int_width n ∧ x < 2 ** n ∧ y < 2 ** n ⇒
  scalar_outcome_value
    (eval_scalar_operation env (UintT n) mode LessThanOp
       [IntegerValue (&x); IntegerValue (&y)]) = ValueOk (bool_value (x < y))
Proof
  simp[eval_scalar_operation_def, scalar_operator_signature_def,
       scalars_have_types_def, uint_typed, scalar_order_key_def,
       scalar_outcome_value_def, bool_value_def]
QED

Theorem uint_equal_op:
  valid_int_width n ∧ x < 2 ** n ∧ y < 2 ** n ⇒
  scalar_outcome_value
    (eval_scalar_operation env (UintT n) mode EqualOp
       [IntegerValue (&x); IntegerValue (&y)]) = ValueOk (bool_value (x = y))
Proof
  simp[eval_scalar_operation_def, scalar_operator_signature_def,
       scalars_have_types_def, uint_typed, scalar_outcome_value_def,
       bool_value_def, is_equality_type_def]
QED

Theorem bool_equal_op:
  scalar_outcome_value
    (eval_scalar_operation env BoolT mode EqualOp [BoolValue a; BoolValue b]) =
  ValueOk (bool_value (a = b))
Proof
  simp[eval_scalar_operation_def, scalar_operator_signature_def,
       scalars_have_types_def, scalar_has_type_def,
       elementary_scalar_has_type_def, scalar_outcome_value_def,
       bool_value_def, is_equality_type_def]
QED

Theorem bool_not_op:
  scalar_outcome_value
    (eval_scalar_operation env BoolT mode BoolNotOp [BoolValue b]) =
  ValueOk (bool_value (¬b))
Proof
  simp[eval_scalar_operation_def, scalar_operator_signature_def,
       scalars_have_types_def, scalar_has_type_def,
       elementary_scalar_has_type_def, scalar_outcome_value_def,
       bool_value_def]
QED

Theorem uint_copy_conversion:
  valid_int_width n ∧ x < 2 ** n ⇒
  eval_conversion env (UintT n) (UintT n) (IntegerValue (&x)) =
  ScalarOk (IntegerValue (&x))
Proof
  strip_tac >>
  simp[eval_conversion_def, core_convertible_def, elementary_convertible_def,
       uint_typed, convert_scalar_def] >>
  irule wrap_integer_id >> gvs[valid_int_width_def, uint_in_range]
QED

Theorem bool_copy_conversion:
  eval_conversion env BoolT BoolT (BoolValue b) = ScalarOk (BoolValue b)
Proof
  simp[eval_conversion_def, core_convertible_def, elementary_convertible_def,
       scalar_has_type_def, elementary_scalar_has_type_def, convert_scalar_def]
QED

(* Results of division stay in range *)

Theorem uint_div_range:
  x < N ⇒ x DIV y < N
Proof
  strip_tac >> Cases_on ‘y = 0’ >> simp[] >>
  ‘x DIV y ≤ x’ by simp[DIV_LESS_EQ] >> decide_tac
QED

Theorem uint_mod_range:
  x < N ∧ y ≠ 0 ⇒ x MOD y < N
Proof
  strip_tac >> irule LESS_EQ_LESS_TRANS >> qexists_tac ‘x’ >> simp[MOD_LESS_EQ]
QED

Theorem uint_mod_divisor_range:
  y ≠ 0 ∧ y < N ⇒ x MOD y < N
Proof
  strip_tac >> irule LESS_TRANS >> qexists_tac ‘y’ >> simp[]
QED

(* Signed integers, and the integer operations without a dedicated form
 * above (unchecked arithmetic, exponentiation, shifts, bitwise operators, all
 * signed arithmetic): the evaluator's own operation on HOL integers. *)

Definition int_value_def:
  int_value (i : int) = ScalarValue (IntegerValue i)
End

Definition int_op_def:
  int_op mode signed n op (xs : int list) =
    case eval_integer_operation mode signed n op (MAP IntegerValue xs) of
      ScalarOk (IntegerValue i) => Returns i
    | ScalarPanic c => Panics c
    | _ => Panics 0
End

Definition uint_op_def:
  uint_op mode n op xs =
    case int_op mode F n op xs of
      Returns i => Returns (Num i)
    | Reverts bs => Reverts bs
    | Panics c => Panics c
End

Theorem int_op_range:
  ∀mode signed n op xs r.
    int_op mode signed n op xs = Returns r ⇒ integer_in_range signed n r
Proof
  rw[int_op_def, AllCaseEqs()] >> drule eval_integer_operation_in_range >>
  rw[] >> gvs[]
QED

Theorem uint_op_range:
  ∀mode n op xs r. uint_op mode n op xs = Returns r ⇒ r < 2 ** n
Proof
  rw[uint_op_def, AllCaseEqs()] >> drule int_op_range >>
  rw[integer_in_range_def] >> intLib.ARITH_TAC
QED

(* An operation whose operands and result have the type's width *)
Definition int_operation_typed_def:
  int_operation_typed env ty op args ⇔
    case scalar_operator_signature op ty of
      SOME (tys, rty) => rty = ty ∧ scalars_have_types env tys args
    | NONE => F
End

Theorem int_operation_eval[local]:
  int_operation_typed env ty op args ∧
  (ty = UintT n ∧ ¬signed ∨ ty = IntT n ∧ signed) ∧ valid_int_width n ⇒
  eval_scalar_operation env ty mode op args =
  eval_integer_operation mode signed n op args
Proof
  rw[int_operation_typed_def, AllCaseEqs()] >>
  Cases_on ‘op’ >> gvs[scalar_operator_signature_def, AllCaseEqs()] >>
  simp[eval_scalar_operation_def, scalar_operator_signature_def] >>
  rpt (CASE_TAC >> gvs[])
QED

Theorem int_operation_progress[local]:
  int_operation_typed env ty op args ∧
  (ty = UintT n ∧ ¬signed ∨ ty = IntT n ∧ signed) ∧ valid_int_width n ⇒
  eval_integer_operation mode signed n op args ≠ ScalarInvalid
Proof
  strip_tac >>
  ‘eval_scalar_operation env ty mode op args =
   eval_integer_operation mode signed n op args’
    by (irule int_operation_eval >> metis_tac[]) >>
  pop_assum (rewrite_tac o single o GSYM) >>
  gvs[int_operation_typed_def] >> BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  irule eval_scalar_operation_progress >>
  simp[core_scalar_type_def, is_value_type_def, is_function_type_def,
       valid_type_shape_def, declared_type_ok_def] >> metis_tac[]
QED

Theorem uint_op_eval:
  int_operation_typed env (UintT n) op (MAP IntegerValue xs) ∧
  valid_int_width n ∧
  ¬(mode = CheckedArithmetic ∧ MEM op [AddOp; SubtractOp; MultiplyOp]) ∧
  op ≠ DivideOp ∧ op ≠ RemainderOp ⇒
  scalar_outcome_value
    (eval_scalar_operation env (UintT n) mode op (MAP IntegerValue xs)) =
  result_outcome uint_value (uint_op mode n op xs)
Proof
  strip_tac >>
  ‘eval_integer_operation mode F n op (MAP IntegerValue xs) ≠ ScalarInvalid’
    by (irule int_operation_progress >> simp[] >> metis_tac[]) >>
  drule int_operation_eval >> simp[] >> disch_then kall_tac >>
  simp[uint_op_def, int_op_def] >>
  Cases_on ‘eval_integer_operation mode F n op (MAP IntegerValue xs)’ >>
  gvs[scalar_outcome_value_def, result_outcome_def] >>
  drule eval_integer_operation_in_range >> rw[] >>
  gvs[integer_in_range_def, uint_value_def, INT_OF_NUM]
QED

Theorem int_op_eval:
  int_operation_typed env (IntT n) op (MAP IntegerValue xs) ∧
  valid_int_width n ⇒
  scalar_outcome_value
    (eval_scalar_operation env (IntT n) mode op (MAP IntegerValue xs)) =
  result_outcome int_value (int_op mode T n op xs)
Proof
  strip_tac >>
  ‘eval_integer_operation mode T n op (MAP IntegerValue xs) ≠ ScalarInvalid’
    by (irule int_operation_progress >> simp[] >> metis_tac[]) >>
  drule int_operation_eval >> simp[] >> disch_then kall_tac >>
  simp[int_op_def] >>
  Cases_on ‘eval_integer_operation mode T n op (MAP IntegerValue xs)’ >>
  gvs[scalar_outcome_value_def, result_outcome_def] >>
  drule eval_integer_operation_in_range >> rw[] >> simp[int_value_def]
QED

(* The same at the operand lists the evaluator builds *)
Theorem uint_op_eval1 = Q.INST [‘xs’ |-> ‘[i]’] uint_op_eval |> SIMP_RULE list_ss [];
Theorem uint_op_eval2 = Q.INST [‘xs’ |-> ‘[i; j]’] uint_op_eval |> SIMP_RULE list_ss [];
Theorem int_op_eval1 = Q.INST [‘xs’ |-> ‘[i]’] int_op_eval |> SIMP_RULE list_ss [];
Theorem int_op_eval2 = Q.INST [‘xs’ |-> ‘[i; j]’] int_op_eval |> SIMP_RULE list_ss [];

(* Addresses and fixed bytes *)

Definition address_value_def:
  address_value (a : address) = ScalarValue (AddressValue a)
End

Definition bytes_value_def:
  bytes_value (bs : byte list) = ScalarValue (BytesValue bs)
End

Definition bytes_op_def:
  bytes_op n op xs =
    case eval_bytes_operation n op (MAP BytesValue xs) of
      ScalarOk (BytesValue bs) => if LENGTH bs = n then Returns bs else Panics 0
    | ScalarPanic c => Panics c
    | _ => Panics 0
End

Theorem bytes_op_range:
  ∀n op xs bs. bytes_op n op xs = Returns bs ⇒ LENGTH bs = n
Proof
  rw[bytes_op_def, AllCaseEqs()] >> simp[]
QED

Theorem bytes_op_eval:
  int_operation_typed env (FixedBytesT n) op (MAP BytesValue xs) ∧
  valid_fixed_bytes_width n ⇒
  scalar_outcome_value
    (eval_scalar_operation env (FixedBytesT n) mode op (MAP BytesValue xs)) =
  result_outcome bytes_value (bytes_op n op xs)
Proof
  strip_tac >>
  ‘eval_scalar_operation env (FixedBytesT n) mode op (MAP BytesValue xs) ≠
   ScalarInvalid’
    by (gvs[int_operation_typed_def] >> BasicProvers.EVERY_CASE_TAC >> gvs[] >>
        irule eval_scalar_operation_progress >>
        simp[core_scalar_type_def, is_value_type_def, is_function_type_def,
             valid_type_shape_def, declared_type_ok_def] >> metis_tac[]) >>
  gvs[int_operation_typed_def] >>
  Cases_on ‘scalar_operator_signature op (FixedBytesT n)’ >> gvs[] >>
  rename1 ‘SOME p’ >> PairCases_on ‘p’ >> gvs[] >>
  ‘eval_scalar_operation env (FixedBytesT n) mode op (MAP BytesValue xs) =
   eval_bytes_operation n op (MAP BytesValue xs)’
    by (Cases_on ‘op’ >> gvs[scalar_operator_signature_def, AllCaseEqs()] >>
        simp[eval_scalar_operation_def, scalar_operator_signature_def] >>
        rpt (CASE_TAC >> gvs[])) >>
  qpat_x_assum ‘eval_scalar_operation _ _ _ _ _ = _’ (fn th => fs[th]) >>
  simp[bytes_op_def] >>
  Cases_on ‘eval_bytes_operation n op (MAP BytesValue xs)’ >>
  gvs[scalar_outcome_value_def, result_outcome_def] >>
  drule_all eval_bytes_operation_canonical >> rw[] >> simp[bytes_value_def]
QED

Theorem bytes_op_eval1 = Q.INST [‘xs’ |-> ‘[a]’] bytes_op_eval |> SIMP_RULE list_ss [];
Theorem bytes_op_eval2 = Q.INST [‘xs’ |-> ‘[a; b]’] bytes_op_eval |> SIMP_RULE list_ss [];

Theorem int_less_op:
  valid_int_width n ∧ integer_in_range T n i ∧ integer_in_range T n j ⇒
  scalar_outcome_value
    (eval_scalar_operation env (IntT n) mode LessThanOp
       [IntegerValue i; IntegerValue j]) = ValueOk (bool_value (i < j))
Proof
  simp[eval_scalar_operation_def, scalar_operator_signature_def,
       scalars_have_types_def, scalar_has_type_def,
       elementary_scalar_has_type_def, scalar_order_key_def,
       scalar_outcome_value_def, bool_value_def, is_ordered_type_def]
QED

Theorem int_equal_op:
  valid_int_width n ∧ integer_in_range T n i ∧ integer_in_range T n j ⇒
  scalar_outcome_value
    (eval_scalar_operation env (IntT n) mode EqualOp
       [IntegerValue i; IntegerValue j]) = ValueOk (bool_value (i = j))
Proof
  simp[eval_scalar_operation_def, scalar_operator_signature_def,
       scalars_have_types_def, scalar_has_type_def,
       elementary_scalar_has_type_def, scalar_outcome_value_def,
       bool_value_def, is_equality_type_def]
QED

(* Conversions between integer types: extension keeps the value, anything
 * else wraps *)

Theorem uint_conversion:
  valid_int_width m ∧ valid_int_width n ∧ x < 2 ** m ⇒
  eval_conversion env (UintT m) (UintT n) (IntegerValue (&x)) =
  ScalarOk (IntegerValue (&(if m ≤ n then x else x MOD 2 ** n)))
Proof
  strip_tac >>
  simp[eval_conversion_def, core_convertible_def, elementary_convertible_def,
       uint_typed, convert_scalar_def, wrap_integer_def] >>
  rw[] >> irule LESS_LESS_EQ_TRANS >> qexists_tac ‘2 ** m’ >> simp[]
QED

Theorem int_conversion:
  valid_int_width m ∧ valid_int_width n ∧ integer_in_range T m i ⇒
  eval_conversion env (IntT m) (IntT n) (IntegerValue i) =
  ScalarOk (IntegerValue (if m ≤ n then i else wrap_integer T n i))
Proof
  strip_tac >>
  simp[eval_conversion_def, core_convertible_def, elementary_convertible_def,
       scalar_has_type_def, elementary_scalar_has_type_def,
       convert_scalar_def] >>
  rw[] >> irule wrap_integer_id >> gvs[valid_int_width_def] >>
  gvs[integer_in_range_def] >>
  ‘2 ** (m - 1) ≤ 2 ** (n - 1)’ by simp[] >> conj_tac
  >- (irule INT_LE_TRANS >> qexists_tac ‘-&(2 ** (m - 1))’ >> simp[])
  >- (irule INT_LTE_TRANS >> qexists_tac ‘&(2 ** (m - 1))’ >> simp[])
QED

Theorem uint_int_conversion:
  valid_int_width n ∧ x < 2 ** n ⇒
  eval_conversion env (UintT n) (IntT n) (IntegerValue (&x)) =
  ScalarOk (IntegerValue (wrap_integer T n (&x)))
Proof
  strip_tac >>
  simp[eval_conversion_def, core_convertible_def, elementary_convertible_def,
       uint_typed, convert_scalar_def]
QED

Theorem int_uint_conversion:
  valid_int_width n ∧ integer_in_range T n i ⇒
  eval_conversion env (IntT n) (UintT n) (IntegerValue i) =
  ScalarOk (IntegerValue (&Num (wrap_integer F n i)))
Proof
  strip_tac >>
  simp[eval_conversion_def, core_convertible_def, elementary_convertible_def,
       scalar_has_type_def, elementary_scalar_has_type_def,
       convert_scalar_def] >>
  ‘integer_in_range F n (wrap_integer F n i)’ by simp[wrap_integer_in_range] >>
  gvs[integer_in_range_def] >> intLib.ARITH_TAC
QED

Theorem uint_wrap_range:
  2 ** n ≤ m ⇒ Num (wrap_integer F n i) < m
Proof
  ‘integer_in_range F n (wrap_integer F n i)’ by simp[wrap_integer_in_range] >>
  gvs[integer_in_range_def] >> intLib.ARITH_TAC
QED

(* Scopes. A loop's effect on its enclosing scopes is a list of writes,
 * set_bindings. Two results of writes to the same scopes are equal when
 * every lookup agrees (same_frames_ext). *)

Definition set_binding_def:
  (set_binding x v [] = []) ∧
  (set_binding x v (scope :: scopes) =
    case FLOOKUP scope (ast_key x) of
      SOME b => (scope |+ (ast_key x, b with binding_value := v)) :: scopes
    | NONE => scope :: set_binding x v scopes)
End

Definition set_bindings_def:
  (set_bindings [] scopes = scopes) ∧
  (set_bindings ((x, v) :: ws) scopes = set_binding x v (set_bindings ws scopes))
End

Theorem update_binding_set_binding:
  update_binding x v scopes =
  if IS_SOME (lookup_binding x scopes) then SOME (set_binding x v scopes)
  else NONE
Proof
  Induct_on ‘scopes’ >>
  rw[update_binding_def, lookup_binding_def, set_binding_def] >>
  Cases_on ‘FLOOKUP h (ast_key x)’ >> gvs[]
QED

Theorem lookup_set_binding:
  lookup_binding y (set_binding x v scopes) =
  if ast_key y = ast_key x then
    OPTION_MAP (λb. b with binding_value := v) (lookup_binding x scopes)
  else lookup_binding y scopes
Proof
  Induct_on ‘scopes’ >> simp[set_binding_def, lookup_binding_def] >>
  rw[] >> rpt (CASE_TAC >> gvs[lookup_binding_def, FLOOKUP_UPDATE])
QED

(* a is scopes with the values of some bindings changed: same frames, same
 * keys, and a key shadowed by an inner frame is untouched further out. *)
Definition same_frames_def:
  (same_frames [] a ⇔ a = []) ∧
  (same_frames (scope :: scopes) a ⇔
    ∃scope' a'.
      a = scope' :: a' ∧ FDOM scope' = FDOM scope ∧ same_frames scopes a' ∧
      ∀k. k ∈ FDOM scope ⇒
          MAP (λs. FLOOKUP s k) a' = MAP (λs. FLOOKUP s k) scopes)
End

Theorem same_frames_refl:
  same_frames scopes scopes
Proof
  Induct_on ‘scopes’ >> simp[same_frames_def]
QED

Theorem flookups_set_binding[local]:
  ast_key x ≠ k ⇒
  MAP (λs. FLOOKUP s k) (set_binding x v a) = MAP (λs. FLOOKUP s k) a
Proof
  Induct_on ‘a’ >> rw[set_binding_def] >> CASE_TAC >> simp[FLOOKUP_UPDATE]
QED

Theorem same_frames_set_binding:
  same_frames scopes a ⇒ same_frames scopes (set_binding x v a)
Proof
  qid_spec_tac ‘a’ >> Induct_on ‘scopes’ >> simp[same_frames_def, set_binding_def] >> rw[] >>
  simp[set_binding_def] >> CASE_TAC >> simp[]
  >- (gvs[flookup_thm] >> rw[] >>
      ‘ast_key x ≠ k’ by (strip_tac >> gvs[]) >>
      simp[flookups_set_binding])
  >- (gvs[flookup_thm] >> simp[pred_setTheory.ABSORPTION_RWT])
QED

Theorem lookup_flookups[local]:
  ∀a b. MAP (λs. FLOOKUP s (ast_key x)) a = MAP (λs. FLOOKUP s (ast_key x)) b ⇒
        lookup_binding x a = lookup_binding x b
Proof
  Induct >> Cases_on ‘b’ >> rw[lookup_binding_def] >> CASE_TAC >> gvs[] >>
  first_x_assum irule >> simp[]
QED

Theorem same_frames_ext:
  ∀scopes a b.
    same_frames scopes a ∧ same_frames scopes b ∧
    (∀n. lookup_binding (AstId n) a = lookup_binding (AstId n) b) ⇒ a = b
Proof
  Induct >> simp[same_frames_def] >> rw[] >>
  ‘∀n. n ∈ FDOM h ⇒ FLOOKUP scope' n = FLOOKUP scope'' n’
    by (rw[] >>
        qpat_x_assum ‘∀n. lookup_binding _ _ = _’ (qspec_then ‘n’ mp_tac) >>
        ‘n ∈ FDOM scope' ∧ n ∈ FDOM scope''’ by simp[] >>
        gvs[lookup_binding_def, ast_key_def, FLOOKUP_DEF]) >>
  conj_tac
  >- (simp[fmap_eq_flookup] >> rw[] >> Cases_on ‘x ∈ FDOM h’ >>
      gvs[FLOOKUP_DEF]) >>
  first_x_assum irule >> simp[] >> rw[] >> Cases_on ‘n ∈ FDOM h’
  >- (irule lookup_flookups >> simp[ast_key_def]) >>
  qpat_x_assum ‘∀n. lookup_binding _ _ = _’ (qspec_then ‘n’ mp_tac) >>
  ‘n ∉ FDOM scope' ∧ n ∉ FDOM scope''’ by simp[] >>
  gvs[lookup_binding_def, ast_key_def, FLOOKUP_DEF]
QED

(* A loop's completion when its helper's result is r: the helper returning
 * means the loop finished normally. *)
Definition loop_completion_def:
  loop_completion r =
    case r of
      Returns _ => NormalCompletion
    | Reverts bs => RevertCompletion bs
    | Panics c => PanicCompletion c
End

(* The evaluator's equations with each intermediate result named by a
 * constant that unfolds only once that result is a record literal, so that
 * rewriting never duplicates an unevaluated eval_stmt. *)

Definition block_next_def:
  block_next n env ss (r : source_result) =
    if r.completion = NormalCompletion
    then eval_block n env ss r.state r.unused_gas_evidence
    else r
End

Definition call_finish_def:
  call_finish p st (r : source_result) =
    abrupt_result (procedure_completion p r) (restore_caller st r.state)
      r.unused_gas_evidence
End

Definition loop_body_def:
  loop_body n env prelude c bd (r2 : source_result) =
    case loop_after_body r2.completion of
      LoopExit => r2 with completion := NormalCompletion
    | LoopStop => r2
    | LoopNext =>
        if n = 0 then r2 with completion := FuelExhausted
        else eval_loop (n - 1) env prelude c bd r2.state
               r2.unused_gas_evidence
End

Definition loop_prelude_def:
  loop_prelude n env prelude c bd (r1 : source_result) =
    if r1.completion ≠ NormalCompletion then pop_result r1 else
    case branch_of r1.state c of
      NONE =>
        pop_result
          (r1 with completion := InvalidCompletion "non-boolean condition")
    | SOME b =>
        if ¬b then pop_result r1 else
        loop_body n env prelude c bd
          (pop_result (eval_block n env bd r1.state r1.unused_gas_evidence))
End

Theorem eval_block_cons:
  eval_block n env (stmt :: ss) st gas = block_next n env ss (eval_stmt n env stmt st gas)
Proof
  simp[Once eval_block_def, block_next_def]
QED

Theorem eval_loop_unfold:
  eval_loop n env prelude c bd st gas =
  loop_prelude n env prelude c bd (eval_block n env prelude (push_scope st) gas)
Proof
  simp[Once eval_block_def, loop_prelude_def, loop_body_def]
QED

Theorem invoke_source_unfold:
  invoke_source n env fid args st gas =
  if n = 0 then abrupt_result FuelExhausted st gas else
  case lookup_procedure env fid of
    NONE => abrupt_result (InvalidCompletion "unknown procedure") st gas
  | SOME p =>
      case entry_scope env p args of
        NONE => abrupt_result (InvalidCompletion "bad arguments") st gas
      | SOME scope =>
          call_finish p st
            (eval_block (n - 1) env p.body (enter_procedure st scope) gas)
Proof
  simp[Once eval_block_def, call_finish_def]
QED

Theorem result_literal_eqs:
  block_next n env ss <| completion := c; state := st'; unused_gas_evidence := g |> =
    (if c = NormalCompletion then eval_block n env ss st' g
     else <| completion := c; state := st'; unused_gas_evidence := g |>) ∧
  call_finish p st <| completion := c; state := st'; unused_gas_evidence := g |> =
    abrupt_result
      (procedure_completion p
         <| completion := c; state := st'; unused_gas_evidence := g |>)
      (restore_caller st st') g ∧
  loop_prelude n env prelude cnd bd
    <| completion := c; state := st'; unused_gas_evidence := g |> =
    (if c ≠ NormalCompletion
     then pop_result <| completion := c; state := st'; unused_gas_evidence := g |>
     else
       case branch_of st' cnd of
         NONE =>
           pop_result
             <| completion := InvalidCompletion "non-boolean condition";
                state := st'; unused_gas_evidence := g |>
       | SOME b =>
           if ¬b then
             pop_result <| completion := c; state := st'; unused_gas_evidence := g |>
           else
             loop_body n env prelude cnd bd
               (pop_result (eval_block n env bd st' g))) ∧
  loop_body n env prelude cnd bd
    <| completion := c; state := st'; unused_gas_evidence := g |> =
    (case loop_after_body c of
       LoopExit => <| completion := NormalCompletion; state := st';
                      unused_gas_evidence := g |>
     | LoopStop => <| completion := c; state := st'; unused_gas_evidence := g |>
     | LoopNext =>
         if n = 0 then
           <| completion := FuelExhausted; state := st'; unused_gas_evidence := g |>
         else eval_loop (n - 1) env prelude cnd bd st' g) ∧
  bind_call_result x ty
    <| completion := c; state := st'; unused_gas_evidence := g |> =
    (case c of
       ReturnCompletion vs =>
         normal_result (define_binding x ty (pack_results vs) st') g
     | _ => <| completion := c; state := st'; unused_gas_evidence := g |>) ∧
  pop_result <| completion := c; state := st'; unused_gas_evidence := g |> =
    <| completion := c; state := st' with scopes := pop_scopes st'.scopes;
       unused_gas_evidence := g |>
Proof
  rw[block_next_def, call_finish_def, loop_prelude_def, loop_body_def,
     bind_call_result_def, pop_result_def]
QED

