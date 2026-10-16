(* Scalar semantics: operators and conversions over canonical values.
 *
 * Values carry no dirty bits: IntegerValue holds the mathematical integer, and
 * fixed bytes hold exactly n bytes. "Cleanup" is therefore wrapping into a
 * type's range; cleanup of raw EVM words belongs to the ABI/storage boundary.
 *
 * Behaviour follows the pinned Solidity documentation (SOLIDITY_PIN):
 * docs/types/value-types.rst, docs/types/conversion.rst and the panic codes in
 * docs/control-structures.rst. Inputs are checked against the operator
 * signature and value types; ill-typed input is ScalarInvalid, never a panic.
 *)
Theory solidityScalar
Ancestors
  solidityCoreWf arithmetic integer words
Libs
  cv_transLib wordsLib intLib

Datatype:
  scalar_outcome = ScalarOk scalar | ScalarPanic num | ScalarInvalid
End

Definition panic_arithmetic_def:
  panic_arithmetic = 0x11n
End

Definition panic_division_by_zero_def:
  panic_division_by_zero = 0x12n
End

Definition panic_enum_conversion_def:
  panic_enum_conversion = 0x21n
End

(* Integers *)

Definition integer_in_range_def:
  integer_in_range signed n (i : int) ⇔
    if signed then -&(2 ** (n - 1)) ≤ i ∧ i < &(2 ** (n - 1))
    else 0 ≤ i ∧ i < &(2 ** n)
End

(* Two's complement truncation to n bits. *)
Definition wrap_integer_def:
  wrap_integer signed n (i : int) =
    let m = i % &(2 ** n) in
    if signed ∧ 0 < n ∧ &(2 ** (n - 1)) ≤ m then m - &(2 ** n) else m
End

Theorem wrap_integer_in_range:
  integer_in_range signed n (wrap_integer signed n i)
Proof
  ‘∃M. (2 : num) ** n = M’ by simp[] >>
  ‘0 < M’ by (rw[] >> gvs[]) >>
  ‘0 ≤ i % &M ∧ i % &M < &M’
    by (mp_tac (Q.SPECL [‘i’, ‘&M’] INT_MOD_BOUNDS) >> simp[]) >>
  qabbrev_tac ‘m = i % &M’ >>
  Cases_on ‘n’ >> gvs[EXP, wrap_integer_def, integer_in_range_def] >>
  rw[] >> intLib.ARITH_TAC
QED

Theorem wrap_integer_id:
  0 < n ∧ integer_in_range signed n i ⇒ wrap_integer signed n i = i
Proof
  strip_tac >> Cases_on ‘n’ >> gvs[EXP] >>
  qabbrev_tac ‘H = (2 : num) ** n'’ >>
  gvs[integer_in_range_def, wrap_integer_def, EXP] >>
  Cases_on ‘signed’ >> gvs[]
  >- (Cases_on ‘0 ≤ i’
      >- (‘i % &(2 * H) = i’ by (irule INT_LESS_MOD >> intLib.ARITH_TAC) >>
          simp[] >> intLib.ARITH_TAC) >>
      ‘i % &(2 * H) = i + &(2 * H)’
        by (irule INT_MOD_UNIQUE >> qexists_tac ‘-1’ >> intLib.ARITH_TAC) >>
      simp[] >> intLib.ARITH_TAC) >>
  irule INT_LESS_MOD >> simp[]
QED

Definition integer_result_def:
  integer_result signed n i = ScalarOk (IntegerValue (wrap_integer signed n i))
End

(* Checked overflow panics with 0x11; unchecked arithmetic wraps. *)
Definition arithmetic_result_def:
  arithmetic_result mode signed n i =
    if integer_in_range signed n i then ScalarOk (IntegerValue i)
    else case mode of
           CheckedArithmetic => ScalarPanic panic_arithmetic
         | UncheckedArithmetic => integer_result signed n i
End

Definition mod_exp_def:
  mod_exp (b : num) (e : num) (m : num) =
    if e = 0 then 1 MOD m
    else
      let h = mod_exp ((b * b) MOD m) (e DIV 2) m in
      if EVEN e then h else (b * h) MOD m
Termination
  WF_REL_TAC ‘measure (FST o SND)’ >> rw[] >> irule DIV_LESS >> simp[]
End

(* Exponents range over uint256, so x ** e is never built for a large e:
 * bases 0, 1 and -1 have closed forms, any other base overflows n bits once
 * e ≥ n, and unchecked results use square-and-multiply modulo 2 ** n.
 *)
Definition integer_exponent_def:
  integer_exponent mode signed n (x : int) (e : num) =
    case mode of
      UncheckedArithmetic =>
        integer_result signed n (&mod_exp (Num (x % &(2 ** n))) e (2 ** n))
    | CheckedArithmetic =>
        if x = 0 then arithmetic_result mode signed n (if e = 0 then 1 else 0)
        else if x = 1 then arithmetic_result mode signed n 1
        else if x = -1 then
          arithmetic_result mode signed n (if EVEN e then 1 else -1)
        else if e < n then arithmetic_result mode signed n (x ** e)
        else ScalarPanic panic_arithmetic
End

(* Shifts are never checked. x << y truncates x * 2 ** y; x >> y is
 * x / 2 ** y rounded towards negative infinity. Amounts ≥ n are capped.
 *)
Definition shift_left_def:
  shift_left signed n (x : int) (y : num) =
    if n ≤ y then 0 else wrap_integer signed n (x * &(2 ** y))
End

Definition shift_right_def:
  shift_right n (x : int) (y : num) =
    if n ≤ y then (if x < 0 then -1 else 0) else x / &(2 ** y)
End

(* The binary bitwise operator of op (and, or, xor), at the two word widths
 * used here; monomorphic so that they translate to cv.
 *)
Definition word256_bitwise_def:
  word256_bitwise op (a : 256 word) b =
    case op of
      BitAndOp => word_and a b
    | BitOrOp => word_or a b
    | _ => word_xor a b
End

Definition byte_bitwise_def:
  byte_bitwise op (a : byte) b =
    case op of
      BitAndOp => word_and a b
    | BitOrOp => word_or a b
    | _ => word_xor a b
End

(* Bitwise operators act on n-bit two's complement representatives. *)
Definition integer_bitwise_def:
  integer_bitwise op signed n (x : int) (y : int) =
    let rx = Num (x % &(2 ** n)) in
    let ry = Num (y % &(2 ** n)) in
    wrap_integer signed n
      (&w2n (word256_bitwise op (n2w rx) (n2w ry)))
End

(* Division rounding towards zero and the matching remainder, stated without
 * a side condition (unlike quot/rem) so that they translate to cv. They agree
 * with quot/rem for a non-zero divisor.
 *)
Definition truncating_quot_def:
  (truncating_quot (i : int) (j : int) : int) =
    if 0 < j then
      if 0 ≤ i then &(Num i DIV Num j) else -&(Num (-i) DIV Num j)
    else if 0 ≤ i then -&(Num i DIV Num (-j))
    else &(Num (-i) DIV Num (-j))
End

Definition truncating_rem_def:
  truncating_rem (i : int) (j : int) = i - truncating_quot i j * j
End

Theorem truncating_quot_eq_quot:
  j ≠ 0 ⇒ truncating_quot i j = i quot j
Proof
  rw[truncating_quot_def, int_quot]
QED

Theorem truncating_rem_eq_rem:
  j ≠ 0 ⇒ truncating_rem i j = i rem j
Proof
  rw[truncating_rem_def, int_rem, truncating_quot_eq_quot]
QED

(* Division rounds towards zero; the remainder takes the dividend's sign.
 * Division and remainder by zero panic even in unchecked mode, and
 * type(int).min / -1 is the only division that overflows.
 *)
Definition eval_integer_operation_def:
  eval_integer_operation mode signed n op args =
    case (op, args) of
      (AddOp, [IntegerValue x; IntegerValue y]) =>
        arithmetic_result mode signed n (x + y)
    | (SubtractOp, [IntegerValue x; IntegerValue y]) =>
        arithmetic_result mode signed n (x - y)
    | (MultiplyOp, [IntegerValue x; IntegerValue y]) =>
        arithmetic_result mode signed n (x * y)
    | (DivideOp, [IntegerValue x; IntegerValue y]) =>
        if y = 0 then ScalarPanic panic_division_by_zero
        else arithmetic_result mode signed n (truncating_quot x y)
    | (RemainderOp, [IntegerValue x; IntegerValue y]) =>
        if y = 0 then ScalarPanic panic_division_by_zero
        else integer_result signed n (truncating_rem x y)
    | (ExponentOp, [IntegerValue x; IntegerValue e]) =>
        integer_exponent mode signed n x (Num e)
    | (ShiftLeftOp, [IntegerValue x; IntegerValue y]) =>
        ScalarOk (IntegerValue (shift_left signed n x (Num y)))
    | (ShiftRightOp, [IntegerValue x; IntegerValue y]) =>
        integer_result signed n (shift_right n x (Num y))
    | (BitAndOp, [IntegerValue x; IntegerValue y]) =>
        ScalarOk (IntegerValue (integer_bitwise op signed n x y))
    | (BitOrOp, [IntegerValue x; IntegerValue y]) =>
        ScalarOk (IntegerValue (integer_bitwise op signed n x y))
    | (BitXorOp, [IntegerValue x; IntegerValue y]) =>
        ScalarOk (IntegerValue (integer_bitwise op signed n x y))
    | (NegateOp, [IntegerValue x]) => arithmetic_result mode signed n (-x)
    | (BitNotOp, [IntegerValue x]) => integer_result signed n (-x - 1)
    | _ => ScalarInvalid
End

(* Fixed bytes *)

Definition bytes_to_num_def:
  bytes_to_num (bs : byte list) = FOLDL (λacc b. acc * 256 + w2n b) 0 bs
End

(* Big-endian encoding of v mod 256 ** k in exactly k bytes. *)
Definition num_to_bytes_def:
  (num_to_bytes 0 (v : num) = [] : byte list) ∧
  (num_to_bytes (SUC k) v = num_to_bytes k (v DIV 256) ++ [n2w (v MOD 256)])
End

(* bytesM to bytesN truncates or pads with zeros on the right. *)
Definition resize_bytes_def:
  resize_bytes n (bs : byte list) =
    TAKE n bs ++ REPLICATE (n - LENGTH bs) (0w : byte)
End

Definition bytes_bitwise_def:
  (bytes_bitwise op (a::as) (b::bs) =
    byte_bitwise op a b :: bytes_bitwise op as bs) ∧
  (bytes_bitwise op _ _ = [])
End

Definition bytes_not_def:
  (bytes_not [] = []) ∧
  (bytes_not ((a : byte)::as) = word_1comp a :: bytes_not as)
End

Definition eval_bytes_operation_def:
  eval_bytes_operation n op args =
    case (op, args) of
      (BitAndOp, [BytesValue a; BytesValue b]) =>
        ScalarOk (BytesValue (bytes_bitwise op a b))
    | (BitOrOp, [BytesValue a; BytesValue b]) =>
        ScalarOk (BytesValue (bytes_bitwise op a b))
    | (BitXorOp, [BytesValue a; BytesValue b]) =>
        ScalarOk (BytesValue (bytes_bitwise op a b))
    | (BitNotOp, [BytesValue a]) => ScalarOk (BytesValue (bytes_not a))
    | (ShiftLeftOp, [BytesValue a; IntegerValue y]) =>
        ScalarOk (BytesValue (num_to_bytes n
          (Num (shift_left F (8 * n) (&bytes_to_num a) (Num y)))))
    | (ShiftRightOp, [BytesValue a; IntegerValue y]) =>
        ScalarOk (BytesValue (num_to_bytes n
          (Num (shift_right (8 * n) (&bytes_to_num a) (Num y)))))
    | _ => ScalarInvalid
End

(* Comparisons *)

(* Addresses compare as uint160 and fixed bytes as big-endian integers. *)
Definition scalar_order_key_def:
  (scalar_order_key (IntegerValue i) = SOME i) ∧
  (scalar_order_key (AddressValue a) = SOME (&w2n a)) ∧
  (scalar_order_key (BytesValue bs) = SOME (&bytes_to_num bs)) ∧
  (scalar_order_key _ = NONE)
End

(* Operations *)

Definition scalars_have_types_def:
  (scalars_have_types env [] [] ⇔ T) ∧
  (scalars_have_types env (ty::tys) (s::ss) ⇔
    scalar_has_type env ty s ∧ scalars_have_types env tys ss) ∧
  (scalars_have_types env _ _ ⇔ F)
End

Definition eval_scalar_operation_def:
  eval_scalar_operation env ty mode op args =
    case scalar_operator_signature op ty of
      NONE => ScalarInvalid
    | SOME (operand_tys, _) =>
        if ¬scalars_have_types env operand_tys args then ScalarInvalid
        else
          case (op, args) of
            (EqualOp, [a; b]) => ScalarOk (BoolValue (a = b))
          | (LessThanOp, [a; b]) =>
              (case (scalar_order_key a, scalar_order_key b) of
                 (SOME x, SOME y) => ScalarOk (BoolValue (x < y))
               | _ => ScalarInvalid)
          | (BoolNotOp, [BoolValue b]) => ScalarOk (BoolValue (¬b))
          | _ =>
              (case ty of
                 UintT n => eval_integer_operation mode F n op args
               | IntT n => eval_integer_operation mode T n op args
               | FixedBytesT n => eval_bytes_operation n op args
               | _ => ScalarInvalid)
End

(* Conversions *)

(* Explicit conversions are directed by the target type and the source value;
 * core_convertible restricts the admitted pairs. Integer conversions all
 * truncate or extend in two's complement. Integer/bytes and address/bytes
 * conversions are big-endian re-encodings between equal sizes. Conversion to
 * an enum panics with 0x21 when out of range, even in unchecked mode.
 * User-defined value types share their underlying representation.
 *)
Definition convert_scalar_def:
  convert_scalar env dst s =
    case (dst, s) of
      (UintT n, IntegerValue i) => ScalarOk (IntegerValue (wrap_integer F n i))
    | (IntT n, IntegerValue i) => ScalarOk (IntegerValue (wrap_integer T n i))
    | (UintT n, BytesValue bs) => ScalarOk (IntegerValue (&bytes_to_num bs))
    | (UintT n, AddressValue a) => ScalarOk (IntegerValue (&w2n a))
    | (FixedBytesT n, BytesValue bs) => ScalarOk (BytesValue (resize_bytes n bs))
    | (FixedBytesT n, IntegerValue i) =>
        ScalarOk (BytesValue (num_to_bytes n (Num i)))
    | (FixedBytesT n, AddressValue a) =>
        ScalarOk (BytesValue (num_to_bytes n (w2n a)))
    | (AddressT _, AddressValue a) => ScalarOk s
    | (AddressT _, IntegerValue i) => ScalarOk (AddressValue (n2w (Num i)))
    | (AddressT _, BytesValue bs) => ScalarOk (AddressValue (n2w (bytes_to_num bs)))
    | (EnumT id, IntegerValue i) =>
        (case lookup_enum env id of
           SOME members =>
             if 0 ≤ i ∧ i < &members then ScalarOk s
             else ScalarPanic panic_enum_conversion
         | NONE => ScalarInvalid)
    | (UserValueT _, _) => ScalarOk s
    | (BoolT, BoolValue _) => ScalarOk s
    | _ => ScalarInvalid
End

Definition eval_conversion_def:
  eval_conversion env src dst s =
    if core_convertible env src dst ∧ scalar_has_type env src s
    then convert_scalar env dst s
    else ScalarInvalid
End

(* cv translation, so the evaluator can run scalar steps under cv_compute. *)

val wrap_integer_pre_def = cv_auto_trans_pre "wrap_integer_pre" wrap_integer_def;

Theorem wrap_integer_pre[cv_pre]:
  ∀signed n i. wrap_integer_pre signed n i
Proof
  rw[wrap_integer_pre_def]
QED

val integer_exponent_pre_def =
  cv_auto_trans_pre "integer_exponent_pre" integer_exponent_def;

Theorem integer_exponent_pre[cv_pre]:
  ∀mode signed n x e. integer_exponent_pre mode signed n x e
Proof
  rw[integer_exponent_pre_def]
QED

val shift_right_pre_def = cv_auto_trans_pre "shift_right_pre" shift_right_def;

Theorem shift_right_pre[cv_pre]:
  ∀n x y. shift_right_pre n x y
Proof
  rw[shift_right_pre_def]
QED

val integer_bitwise_pre_def =
  cv_auto_trans_pre "integer_bitwise_pre" integer_bitwise_def;

Theorem integer_bitwise_pre[cv_pre]:
  ∀op signed n x y. integer_bitwise_pre op signed n x y
Proof
  rw[integer_bitwise_pre_def]
QED

val () = cv_auto_trans eval_scalar_operation_def;
val () = cv_auto_trans eval_conversion_def;
