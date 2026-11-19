(* Memory as the compiled code holds it: the frame's EVM memory, a byte per
 * address with its active size (solidityState), laid out as solc 0.8.37's
 * IR code generator lays it out with the optimizer off. The free memory
 * pointer is the word at 0x40; objects are allocated there. A byte sequence
 * is its length word, then its bytes; a dynamic array its length word, then
 * a word per element; a static array a word per element; a struct a word per
 * field. A byte sequence or dynamic array nobody allocated is the zero slot
 * 0x60, whose length word is zero. A word of a value type holds the value as
 * the compiler's cleanup leaves it; a word of a reference type, the address
 * of its object.
 *
 * Every access raises the active size as the compiled code's own access does
 * (an mload a word, an mstore8 a byte). Addresses are unbounded numbers, as in
 * the Yul evaluator's memory: an access the EVM could not pay for has no
 * meaning here. *)
Theory solidityMemory
Ancestors
  solidityStorage yulEvaluator
Libs
  cv_transLib wordsLib intLib

(* Byte access *)

Definition memory_touch_def:
  memory_touch a n (st : source_state) =
    st with memory_size := touched_size st.memory_size a n
End

Definition memory_read_def:
  memory_read a n (st : source_state) =
    (yul_mem_read st.memory a n, memory_touch a n st)
End

Definition memory_write_def:
  memory_write a bs (st : source_state) =
    memory_touch a (LENGTH bs) st with memory := yul_mem_write st.memory a bs
End

(* mload and mstore *)
Definition memory_load_def:
  memory_load a st =
    let (bs, st1) = memory_read a 32 st in (num_of_be_bytes bs, st1)
End

Definition memory_store_def:
  memory_store a (n : num) st = memory_write a (num_to_bytes 32 n) st
End

(* Allocation: finalize_allocation moves the free memory pointer from p past
 * size bytes rounded up to a word, Panic(0x41) when the new pointer passes
 * 2^64 - 1 or wraps; allocate_memory allocates at the free memory pointer. *)
Definition finalize_allocation_def:
  finalize_allocation p size st =
    let q = (p + (size + 31) MOD 2 ** 256 DIV 32 * 32) MOD 2 ** 256 in
    if 2 ** 64 ≤ q ∨ q < p then INR (PanicCompletion 65)
    else INL (memory_store 64 q st)
End

Definition allocate_memory_def:
  allocate_memory size st =
    let (p, st1) = memory_load 64 st in
    case finalize_allocation p size st1 of
      INL st2 => INL (p, st2)
    | INR c => INR c
End

(* allocate_memory_array for a byte sequence of n bytes: Panic(0x41) past
 * 2^64 - 1 bytes; its length word written, its data not. *)
Definition allocate_byte_array_def:
  allocate_byte_array n st =
    if 2 ** 64 ≤ n then INR (PanicCompletion 65) else
    case allocate_memory ((n + 31) DIV 32 * 32 + 32) st of
      INL (p, st1) => INL (p, memory_store p n st1)
    | INR c => INR c
End

(* The copies with cleanup (calldatacopy or mcopy) write a zero word after
 * the bytes they copy. *)
Definition copy_with_cleanup_def:
  copy_with_cleanup a bs st =
    memory_write (a + LENGTH bs) (REPLICATE 32 0w) (memory_write a bs st)
End

(* A new byte sequence holding bs, its bytes copied with cleanup, as the
 * decoders and copies from calldata and memory make it. *)
Definition new_byte_array_def:
  new_byte_array bs st =
    case allocate_byte_array (LENGTH bs) st of
      INL (p, st1) => INL (p, copy_with_cleanup (p + 32) bs st1)
    | INR c => INR c
End

(* Words *)

(* The type a value type's word is read and written as: a user-defined value
 * type's underlying type, a contract's address. *)
Definition word_type_def:
  word_type env ty =
    case ty of
      UserValueT id => lookup_user_value env id
    | ContractT _ => SOME (AddressT NonpayableAddress)
    | _ => SOME ty
End

(* A value-type scalar as the word the compiler keeps it in: integers and
 * enums in two's complement, fixed bytes left-aligned. *)
Definition scalar_word_def:
  scalar_word env ty s =
    case word_type env ty of
      SOME (FixedBytesT k) =>
        OPTION_MAP (λn. n * 2 ** (8 * (32 - k))) (stored_number k s)
    | SOME _ => stored_number 32 s
    | NONE => NONE
End

(* The word a value of type ty is held in memory as; an external function is
 * its address then its selector, left-aligned. An internal function is the id
 * of its declaration, where the compiler's word is the function's number in
 * its internal dispatch (the artifact's internalFunctionIDs, which the
 * importer does not read yet): the two differ only to code that reads the
 * word itself. *)
Definition memory_word_def:
  memory_word env ty v =
    case v of
      ScalarValue (InternalFunctionValue f) =>
        SOME (case f of NONE => 0 | SOME (AstId n) => n)
    | ScalarValue (ExternalFunctionValue a selector) =>
        if LENGTH selector = 4 then
          SOME (w2n a * 2 ** 96 + num_of_be_bytes selector * 2 ** 64)
        else NONE
    | ScalarValue s => scalar_word env ty s
    | ReferenceValue (MemoryReference p _) => SOME p
    | _ => NONE
End

Definition memory_object_type_def:
  memory_object_type ty ⇔
    case ty of
      BytesT => T
    | StringT => T
    | ArrayT _ _ => T
    | StructT _ => T
    | _ => F
End

(* The value a word of type ty stands for after the compiler's cleanup
 * (read_from_memory): a bool any nonzero word, an integer, address or fixed
 * bytes its own bits, an enum word outside the enum's members Panic(0x21),
 * as its validator does; a reference the object at that address; an
 * internal function the declaration with that id, as in memory_word. *)
Definition word_value_def:
  word_value env ty (w : num) =
    if memory_object_type ty then INL (ReferenceValue (MemoryReference w ty)) else
    case ty of
      EnumT id =>
        (case lookup_enum env id of
           SOME members =>
             if w < members then INL (ScalarValue (IntegerValue (&w)))
             else INR (PanicCompletion 33)
         | NONE => INR (InvalidCompletion "unknown enum"))
    | FunctionT InternalFn _ _ _ =>
        INL (ScalarValue (InternalFunctionValue
               (if w = 0 then NONE else SOME (AstId w))))
    | FunctionT ExternalFn _ _ _ =>
        INL (ScalarValue (ExternalFunctionValue (n2w (w DIV 2 ** 96))
               (num_to_bytes 4 (w DIV 2 ** 64))))
    | _ =>
      case word_type env ty of
        SOME BoolT => INL (ScalarValue (BoolValue (w ≠ 0)))
      | SOME (FixedBytesT k) =>
          (case stored_value (FixedBytesT k) (w DIV 2 ** (8 * (32 - k))) of
             SOME s => INL (ScalarValue s)
           | NONE => INR (InvalidCompletion "bad memory word type"))
      | SOME u =>
          (case storage_bytes u of
             SOME b =>
               (case stored_value u (w MOD 2 ** (8 * b)) of
                  SOME s => INL (ScalarValue s)
                | NONE => INR (InvalidCompletion "bad memory word type"))
           | NONE => INR (InvalidCompletion "bad memory word type"))
      | NONE => INR (InvalidCompletion "bad memory word type")
End

(* The value of type ty in the word at a. *)
Definition read_memory_word_def:
  read_memory_word env ty a st =
    let (w, st1) = memory_load a st in
    case word_value env ty w of
      INL v => INL (v, st1)
    | INR c => INR c
End

Definition write_memory_word_def:
  write_memory_word env ty a v st =
    case memory_word env ty v of
      SOME w => INL (memory_store a w st)
    | NONE => INR (InvalidCompletion "bad memory word value")
End

(* Objects *)

(* The length of the memory array or byte sequence of type ty at p, and where
 * its elements start. *)
Definition memory_length_def:
  memory_length ty p st =
    case ty of
      ArrayT _ (SOME k) => (k, st)
    | _ => memory_load p st
End

Definition memory_data_def:
  memory_data ty (p : num) =
    case ty of
      ArrayT _ (SOME _) => p
    | _ => p + 32
End

(* The word of element i of the memory array at p, and its type;
 * Panic(0x32) when i is out of bounds. *)
Definition memory_array_element_def:
  memory_array_element ty p (i : int) st =
    case ty of
      ArrayT element _ =>
        let (n, st1) = memory_length ty p st in
        if i < 0 ∨ &n ≤ i then INR (PanicCompletion 50)
        else INL (memory_data ty p + 32 * Num i, element, st1)
    | _ => INR (InvalidCompletion "bad memory array reference")
End

(* Byte i of the byte sequence at p; Panic(0x32) when out of bounds. *)
Definition memory_byte_element_def:
  memory_byte_element p (i : int) st =
    let (n, st1) = memory_load p st in
    if i < 0 ∨ &n ≤ i then INR (PanicCompletion 50)
    else INL (p + 32 + Num i, st1)
End

(* The position and type of field f among a struct's fields. *)
Definition field_position_def:
  (field_position (f : ast_id) [] = NONE) ∧
  (field_position f ((g, ty) :: fields) =
    if f = g then SOME (0n, ty : sol_type) else
    case field_position f fields of
      SOME (k, ty') => SOME (k + 1, ty')
    | NONE => NONE)
End

(* The word of field f of the memory struct of type s at p, and its type. *)
Definition memory_struct_field_def:
  memory_struct_field env s p f =
    case lookup_struct env s of
      SOME fields =>
        (case field_position f fields of
           SOME (k, ty) => INL (p + 32 * k, ty)
         | NONE => INR (InvalidCompletion "unknown struct field"))
    | NONE => INR (InvalidCompletion "unknown struct")
End

(* The bytes of the byte sequence at p. *)
Definition memory_bytes_def:
  memory_bytes p st =
    let (n, st1) = memory_load p st in memory_read (p + 32) n st1
End

(* Zero values: zero_value_for_split, allocate_and_zero_memory_array and
 * allocate_and_zero_memory_struct. A value type's zero is the zero word; a
 * byte sequence's or dynamic array's the zero slot; a static array or struct
 * is allocated, then its words zeroed in order, allocating each static array
 * or struct member in turn. A value-type array's words are zeroed at once
 * (zero_memory_chunk). The fuel bounds the struct nesting. *)
Definition zero_value_def:
  (zero_value env (fuel : num) ty st =
    case ty of
      ArrayT element (SOME k) =>
        (case allocate_memory (32 * k) st of
           INL (p, st1) =>
             (case zero_elements env fuel element p k st1 of
                INL st2 => INL (p, st2)
              | INR c => INR c)
         | INR c => INR c)
    | StructT s =>
        (case lookup_struct env s of
           SOME fields =>
             if fuel = 0 then INR (InvalidCompletion "struct nesting") else
             (case allocate_memory (32 * LENGTH fields) st of
                INL (p, st1) =>
                  (case zero_words env (fuel - 1) (MAP SND fields) p st1 of
                     INL st2 => INL (p, st2)
                   | INR c => INR c)
              | INR c => INR c)
         | NONE => INR (InvalidCompletion "unknown struct"))
    | ArrayT _ NONE => INL (96, st)
    | BytesT => INL (96, st)
    | StringT => INL (96, st)
    | _ => INL (0, st)) ∧
  (zero_elements env fuel element p k st =
    if k = 0 then INL st else
    if memory_object_type element then
      (case zero_value env fuel element st of
         INL (w, st1) =>
           zero_elements env fuel element (p + 32) (k - 1) (memory_store p w st1)
       | INR c => INR c)
    else INL (memory_write p (REPLICATE (32 * k) 0w) st)) ∧
  (zero_words env fuel [] p st = INL st) ∧
  (zero_words env fuel (ty :: tys) p st =
    case zero_value env fuel ty st of
      INL (w, st1) => zero_words env fuel tys (p + 32) (memory_store p w st1)
    | INR c => INR c)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (env, fuel, ty, st) => (fuel, sol_type_size ty, 0n)
  | INR (INL (env, fuel, element, p, k, st)) => (fuel, sol_type_size element, k + 1)
  | INR (INR (env, fuel, tys, p, st)) => (fuel, list_size sol_type_size tys, 1))’ >>
  rw[solidityASTTheory.sol_type_size_def, listTheory.list_size_def]
End

(* allocate_and_zero_memory_array for new T[](n) and new bytes(n): Panic(0x41)
 * past 2^64 - 1 elements; the length word, then the zeroed data, a byte
 * sequence's rounded up to a word. *)
Definition new_memory_array_def:
  new_memory_array env ty n st =
    if 2 ** 64 ≤ n then INR (PanicCompletion 65) else
    let size = (case ty of
                  ArrayT _ _ => 32 * n
                | _ => (n + 31) DIV 32 * 32) in
    case allocate_memory (size + 32) st of
      INR c => INR c
    | INL (p, st1) =>
        let st2 = memory_store p n st1 in
        case ty of
          ArrayT element _ =>
            (case zero_elements env (LENGTH env.type_declarations) element (p + 32) n st2 of
               INL st3 => INL (p, st3)
             | INR c => INR c)
        | _ => INL (p, memory_write (p + 32) (REPLICATE size 0w) st2)
End

(* The value of a memory array or struct, as a copy reads it: the tuple of
 * its elements or fields, byte sequences as their bytes. The fuel bounds the
 * struct nesting. *)
Definition memory_value_def:
  (memory_value env (fuel : num) ty v st =
    case (ty, v) of
      (ArrayT element length, ReferenceValue (MemoryReference p rty)) =>
        if rty ≠ ty then INR (InvalidCompletion "bad memory array reference") else
        let (n, st1) = memory_length ty p st in
        (case memory_elements env fuel element (memory_data ty p) n st1 of
           INL (vs, st2) => INL (TupleValue vs, st2)
         | INR c => INR c)
    | (StructT s, ReferenceValue (MemoryReference p rty)) =>
        if rty ≠ ty then INR (InvalidCompletion "bad memory struct reference") else
        (case lookup_struct env s of
           SOME fields =>
             if fuel = 0 then INR (InvalidCompletion "struct nesting") else
             (case memory_fields env (fuel - 1) (MAP SND fields) p st of
                INL (vs, st1) => INL (TupleValue vs, st1)
              | INR c => INR c)
         | NONE => INR (InvalidCompletion "unknown struct"))
    | (_, ReferenceValue (MemoryReference p rty)) =>
        if byte_sequence_type rty then
          let (bs, st1) = memory_bytes p st in INL (ScalarValue (BytesValue bs), st1)
        else INR (InvalidCompletion "bad memory value")
    | (_, ScalarValue _) => INL (v, st)
    | _ => INR (InvalidCompletion "bad memory value")) ∧
  (memory_elements env fuel element p n st =
    if n = 0 then INL ([], st) else
    case read_memory_word env element p st of
      INR c => INR c
    | INL (w, st1) =>
        case memory_value env fuel element w st1 of
          INR c => INR c
        | INL (v, st2) =>
            case memory_elements env fuel element (p + 32) (n - 1) st2 of
              INL (vs, st3) => INL (v :: vs, st3)
            | INR c => INR c) ∧
  (memory_fields env fuel [] p st = INL ([], st)) ∧
  (memory_fields env fuel (ty :: tys) p st =
    case read_memory_word env ty p st of
      INR c => INR c
    | INL (w, st1) =>
        case memory_value env fuel ty w st1 of
          INR c => INR c
        | INL (v, st2) =>
            case memory_fields env fuel tys (p + 32) st2 of
              INL (vs, st3) => INL (v :: vs, st3)
            | INR c => INR c)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (env, fuel, ty, v, st) => (fuel, sol_type_size ty, 0n)
  | INR (INL (env, fuel, element, p, n, st)) => (fuel, sol_type_size element, n + 1)
  | INR (INR (env, fuel, tys, p, st)) => (fuel, list_size sol_type_size tys, 1))’ >>
  rw[solidityASTTheory.sol_type_size_def, listTheory.list_size_def] >>
  qpat_x_assum ‘(_, _) = _’ (assume_tac o SYM) >> gvs[]
End

(* Scalar defaults, for reads of what was never written. *)
Definition default_elementary_def:
  default_elementary ty =
    case ty of
      BoolT => SOME (BoolValue F)
    | UintT _ => SOME (IntegerValue 0)
    | IntT _ => SOME (IntegerValue 0)
    | AddressT _ => SOME (AddressValue 0w)
    | FixedBytesT n => SOME (BytesValue (REPLICATE n 0w))
    | EnumT _ => SOME (IntegerValue 0)
    | FunctionT InternalFn _ _ _ => SOME (InternalFunctionValue NONE)
    | _ => NONE
End

(* The compiler's storage helpers hash a data area's slot in scratch word 0;
 * see read_scratch. *)
Definition scratch_write_def:
  scratch_write (w : bytes32 option) st =
    case w of
      NONE => st
    | SOME w => memory_write 0 (num_to_bytes 32 (w2n w)) st
End

(* The bytes of a byte sequence wherever it is. A calldata one reads zeros
 * past the end of the calldata, as calldatacopy does; its offset and length
 * were checked when decoded. Storage byte access propagates malformed-header
 * panics. *)
Definition byte_contents_def:
  byte_contents (st : source_state) r =
    case r of
      StorageReference _ addr slot _ _ _ =>
        (case storage_byte_contents st.world.accounts r of
           INL bs =>
             INL (bs, scratch_write (long_bytes_scratch st.world.accounts addr slot) st)
         | INR c => INR c)
    | MemoryReference p ty =>
        if byte_sequence_type ty then INL (memory_bytes p st)
        else INR (InvalidCompletion "bad byte sequence reference")
    | CalldataReference offset length ty =>
        if byte_sequence_type ty then
          INL (TAKE length (DROP offset st.frame.call_data ++ REPLICATE length 0w), st)
        else INR (InvalidCompletion "bad byte sequence reference")
    | _ => INR (InvalidCompletion "bad byte sequence reference")
End

(* A byte sequence as an ABI decoder's input: the bytes it holds and its
 * length. A memory one holds only its bytes below the memory size; the
 * bytes past that are zero. *)
Definition decode_source_def:
  decode_source (st : source_state) r =
    case r of
      MemoryReference p ty =>
        if byte_sequence_type ty then
          let (n, st1) = memory_load p st in
          let held = MIN n (st1.memory_size - (p + 32)) in
          INL (yul_mem_read st1.memory (p + 32) held, n, st1)
        else INR (InvalidCompletion "bad byte sequence reference")
    | _ =>
        case byte_contents st r of
          INL (bs, st1) => INL (bs, LENGTH bs, st1)
        | INR c => INR c
End

Definition copy_byte_contents_def:
  copy_byte_contents src dst st =
    case dst of
      StorageReference PersistentStorage dst_addr dst_slot _ _ _ =>
        (case src of
           StorageReference PersistentStorage src_addr src_slot _ _ _ =>
             (case copy_storage_bytes st.world.accounts src dst st.frame.static_context of
                INL accounts =>
                  let accounts0 = st.world.accounts in
                  INL (scratch_write
                    (if IS_SOME (long_bytes_scratch accounts0 src_addr src_slot)
                     then SOME dst_slot
                     else long_bytes_scratch accounts0 dst_addr dst_slot)
                    (st with world := st.world with accounts := accounts))
              | INR c => INR c)
         | _ => case byte_contents st src of
             INR c => INR c
           | INL (bs, st1) =>
               case store_storage_bytes st1.world.accounts dst bs st1.frame.static_context of
                 INL accounts =>
                   INL (scratch_write
                     (if 32 ≤ LENGTH bs then SOME dst_slot
                      else long_bytes_scratch st1.world.accounts dst_addr dst_slot)
                     (st1 with world := st1.world with accounts := accounts))
               | INR c => INR c)
    | _ => INR (InvalidCompletion "bad storage byte copy")
End

(* Reference conversion preserves identity and location; copying is a statement. *)
Definition convert_byte_reference_def:
  convert_byte_reference src dst r =
    case (src, dst, r) of
      (LocatedT MemoryLoc a, LocatedT MemoryLoc b, MemoryReference p c) =>
        if a = c ∧ byte_sequence_type a ∧ byte_sequence_type b then
          ValueOk (ReferenceValue (MemoryReference p b))
        else ValueAbrupt (InvalidCompletion "bad byte reference conversion")
    | (LocatedT CalldataLoc a, LocatedT CalldataLoc b, CalldataReference off len c) =>
        if a = c ∧ byte_sequence_type a ∧ byte_sequence_type b then
          ValueOk (ReferenceValue (CalldataReference off len b))
        else ValueAbrupt (InvalidCompletion "bad byte reference conversion")
    | (LocatedT StorageLoc a, LocatedT StorageLoc b,
       StorageReference PersistentStorage addr slot 0 c layout) =>
        if a = c ∧ byte_sequence_type a ∧ byte_sequence_type b then
          ValueOk (ReferenceValue
            (StorageReference PersistentStorage addr slot 0 b layout))
        else ValueAbrupt (InvalidCompletion "bad byte reference conversion")
    | _ => ValueAbrupt (InvalidCompletion "bad byte reference conversion")
End

val () = cv_auto_trans memory_touch_def;
val () = cv_auto_trans memory_read_def;
val () = cv_auto_trans memory_write_def;
val () = cv_auto_trans memory_load_def;
val () = cv_auto_trans memory_store_def;
val () = cv_auto_trans finalize_allocation_def;
val () = cv_auto_trans allocate_memory_def;
val () = cv_auto_trans allocate_byte_array_def;
val () = cv_auto_trans copy_with_cleanup_def;
val () = cv_auto_trans new_byte_array_def;
val () = cv_auto_trans word_type_def;
val () = cv_auto_trans scalar_word_def;
val () = cv_auto_trans memory_word_def;
val () = cv_auto_trans memory_object_type_def;
val () = cv_auto_trans word_value_def;
val () = cv_auto_trans read_memory_word_def;
val () = cv_auto_trans write_memory_word_def;
val () = cv_auto_trans memory_length_def;
val () = cv_auto_trans memory_data_def;
val () = cv_auto_trans memory_array_element_def;
val () = cv_auto_trans memory_byte_element_def;
val () = cv_auto_trans field_position_def;
val () = cv_auto_trans memory_struct_field_def;
val () = cv_auto_trans memory_bytes_def;

val zero_value_pre_def = cv_auto_trans_pre_rec
  "zero_value_pre zero_elements_pre zero_words_pre" zero_value_def (
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (env, fuel, ty, st) => (cv$c2n fuel, cv_size ty, 0)
  | INR (INL (env, fuel, element, p, k, st)) =>
      (cv$c2n fuel, cv_size element, cv$c2n k + 1)
  | INR (INR (env, fuel, tys, p, st)) => (cv$c2n fuel, cv_size tys, 1))’ >>
  cv_termination_tac
);

Theorem zero_value_pre[cv_pre]:
  (∀env fuel ty st. zero_value_pre env fuel ty st) ∧
  (∀env fuel element p k st. zero_elements_pre env fuel element p k st) ∧
  (∀env fuel tys p st. zero_words_pre env fuel tys p st)
Proof
  ho_match_mp_tac zero_value_ind >> rpt strip_tac >>
  simp[Once zero_value_pre_def] >> rw[] >> gvs[]
QED

val () = cv_auto_trans new_memory_array_def;

val memory_value_pre_def = cv_auto_trans_pre_rec
  "memory_value_pre memory_elements_pre memory_fields_pre" memory_value_def (
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (env, fuel, ty, v, st) => (cv$c2n fuel, cv_size ty, 0)
  | INR (INL (env, fuel, element, p, n, st)) =>
      (cv$c2n fuel, cv_size element, cv$c2n n + 1)
  | INR (INR (env, fuel, tys, p, st)) => (cv$c2n fuel, cv_size tys, 1))’ >>
  cv_termination_tac
);

Theorem memory_value_pre[cv_pre]:
  (∀env fuel ty v st. memory_value_pre env fuel ty v st) ∧
  (∀env fuel element p n st. memory_elements_pre env fuel element p n st) ∧
  (∀env fuel tys p st. memory_fields_pre env fuel tys p st)
Proof
  ho_match_mp_tac memory_value_ind >> rpt strip_tac >>
  simp[Once memory_value_pre_def] >> rw[] >> gvs[]
QED

val () = cv_auto_trans default_elementary_def;
val () = cv_auto_trans scratch_write_def;
val () = cv_auto_trans byte_contents_def;
val () = cv_auto_trans decode_source_def;
val () = cv_auto_trans copy_byte_contents_def;
val () = cv_auto_trans convert_byte_reference_def;
