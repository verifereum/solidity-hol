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

(* Byte access. An address is a word: the compiled code computes addresses
 * with word arithmetic, so one past 2^256 wraps. *)

Definition memory_touch_def:
  memory_touch a n (st : source_state) =
    st with memory_size := touched_size st.memory_size (a MOD 2 ** 256) n
End

Definition memory_read_def:
  memory_read a n (st : source_state) =
    (yul_mem_read st.memory (a MOD 2 ** 256) n, memory_touch a n st)
End

Definition memory_write_def:
  memory_write a bs (st : source_state) =
    memory_touch a (LENGTH bs) st with
      memory := yul_mem_write st.memory (a MOD 2 ** 256) bs
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
 * its address then its selector, left-aligned. An internal function is its
 * number in the compiler's internal dispatch, which starts at 1, and a word
 * no function has, the zero value 0 included, is itself; a function without
 * a number has no word. *)
Definition memory_word_def:
  memory_word env ty v =
    case v of
      ScalarValue (InternalFunctionValue f) =>
        (case f of INL x => ALOOKUP env.function_ids x | INR w => SOME w)
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
 * internal function the function with that dispatch number, as in
 * memory_word, or the word itself when no function has it, which the
 * compiler's dispatch panics on (0x51) only once it is called. A function of
 * another type is left unsupported: the compiler calls it when the number of
 * stack slots its parameters and returns take matches, and panics otherwise. *)
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
        (case FILTER (λ(x, n). n = w) env.function_ids of
           [] => INL (ScalarValue (InternalFunctionValue (INR w)))
         | (x, _) :: _ =>
             if scalar_has_type env ty (InternalFunctionValue (INL x))
             then INL (ScalarValue (InternalFunctionValue (INL x)))
             else INR (InvalidCompletion
                    "unsupported: an internal function word of a function of another type"))
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

(* Run a post-read fail-closed check before surfacing any read failure, so a
 * fail-closed guard takes precedence over a panic or revert from reading inputs. *)
Definition guard_result_def:
  guard_result (check : 'b + source_completion) (r : 'a + source_completion) =
    case check of
      INR c => INR c
    | INL x =>
        case r of
          INL v => INL (v, x)
        | INR c => INR c
End

Definition read_result_def:
  read_result (r, st : source_state) = guard_result (INL st) r
End

(* The value of type ty in the word at a, and the state after loading it
 * (whether or not the word is valid, so callers know what was read). *)
Definition read_memory_word_def:
  read_memory_word env ty a st =
    let (w, st1) = memory_load a st in (word_value env ty w, st1)
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
 * Panic(0x32) when i is out of bounds. Addresses wrap at 2^256, as the
 * compiler's word arithmetic does. *)
Definition memory_array_element_def:
  memory_array_element ty p (i : int) st =
    case ty of
      ArrayT element _ =>
        let (n, st1) = memory_length ty p st in
        if i < 0 ∨ &n ≤ i then INR (PanicCompletion 50)
        else INL ((memory_data ty p + 32 * Num i) MOD 2 ** 256, element, st1)
    | _ => INR (InvalidCompletion "bad memory array reference")
End

(* Byte i of the byte sequence at p; Panic(0x32) when out of bounds. *)
Definition memory_byte_element_def:
  memory_byte_element p (i : int) st =
    let (n, st1) = memory_load p st in
    if i < 0 ∨ &n ≤ i then INR (PanicCompletion 50)
    else INL ((p + 32 + Num i) MOD 2 ** 256, st1)
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

(* The value of a memory array or struct, as the encoder reads it: the tuple
 * of its elements or fields, byte sequences as their bytes. The fuel bounds
 * the struct nesting. *)
Definition memory_value_def:
  (memory_value env (fuel : num) ty v st =
    case (ty, v) of
      (ArrayT element length, ReferenceValue (MemoryReference p rty)) =>
        if rty ≠ ty then (INR (InvalidCompletion "bad memory array reference"), st) else
        let (n, st1) = memory_length ty p st in
        let (r, st2) = memory_elements env fuel element (memory_data ty p) n st1 in
        ((case r of INL vs => INL (TupleValue vs) | INR c => INR c), st2)
    | (StructT s, ReferenceValue (MemoryReference p rty)) =>
        if rty ≠ ty then (INR (InvalidCompletion "bad memory struct reference"), st) else
        (case lookup_struct env s of
           SOME fields =>
             if fuel = 0 then (INR (InvalidCompletion "struct nesting"), st) else
             let (r, st1) = memory_fields env (fuel - 1) (MAP SND fields) p st in
             ((case r of INL vs => INL (TupleValue vs) | INR c => INR c), st1)
         | NONE => (INR (InvalidCompletion "unknown struct"), st))
    | (_, ReferenceValue (MemoryReference p rty)) =>
        if byte_sequence_type rty then
          let (bs, st1) = memory_bytes p st in
          (INL (ScalarValue (BytesValue bs)), st1)
        else (INR (InvalidCompletion "bad memory value"), st)
    | (_, ScalarValue _) => (INL v, st)
    | _ => (INR (InvalidCompletion "bad memory value"), st)) ∧
  (memory_elements env fuel element p n st =
    if n = 0 then (INL [], st) else
    case read_memory_word env element p st of
      (INR c, st1) => (INR c, st1)
    | (INL w, st1) =>
        case memory_value env fuel element w st1 of
          (INR c, st2) => (INR c, st2)
        | (INL v, st2) =>
            let (r, st3) = memory_elements env fuel element (p + 32) (n - 1) st2 in
            ((case r of INL vs => INL (v :: vs) | INR c => INR c), st3)) ∧
  (memory_fields env fuel [] p st = (INL [], st)) ∧
  (memory_fields env fuel (ty :: tys) p st =
    case read_memory_word env ty p st of
      (INR c, st1) => (INR c, st1)
    | (INL w, st1) =>
        case memory_value env fuel ty w st1 of
          (INR c, st2) => (INR c, st2)
        | (INL v, st2) =>
            let (r, st3) = memory_fields env fuel tys (p + 32) st2 in
            ((case r of INL vs => INL (v :: vs) | INR c => INR c), st3))
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
    | FunctionT InternalFn _ _ _ => SOME (InternalFunctionValue (INR 0))
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

(* The memory a decoder's reads of r's bytes touch, up to reach bytes in. *)
Definition decode_reads_def:
  decode_reads r reach (st : source_state) =
    case r of
      MemoryReference p _ => memory_touch (p + 32) reach st
    | _ => st
End

(* How far into r's n bytes a decoder may read before it reaches the free
 * memory pointer free, where the compiled decoder allocates, and so may read
 * what its own allocations wrote. *)
Definition decode_bound_def:
  decode_bound r free (n : num) =
    case r of
      MemoryReference p _ => free - (p + 32)
    | _ => n
End

(* Whether a decoder's reads of r, its length word and up to reach bytes
 * after it, overlap the free memory pointer's word [64, 96), which the
 * compiled decoder rewrites as it allocates. *)
Definition decode_reads_free_pointer_def:
  decode_reads_free_pointer r (reach : num) =
    case r of
      MemoryReference p _ => p < 96 ∧ 64 < p + 32 + reach
    | _ => F
End

(* A byte sequence copied into storage at slot, as the compiled copy
 * (copy_byte_array_to_storage) touches memory: the new length, Panic(0x41) at
 * 2^64 or more, the old length (Panic(0x22) on a bad length tag), the data
 * area's hash in scratch word 0 when the old or the new contents are long,
 * and only then the source's data, from the state after that hash. A memory
 * source's data is read in whole words, the last one too, as the copy loop
 * reads it; bytes another source gave touch no memory. The state reached is
 * returned on a failure too. *)
Definition copy_bytes_to_storage_def:
  copy_bytes_to_storage addr slot v static st =
    case (case v of
            ReferenceValue (MemoryReference p ty) =>
              if byte_sequence_type ty then INL (memory_load p st)
              else INR (InvalidCompletion "bad memory byte sequence")
          | ScalarValue (BytesValue bs) => INL (LENGTH bs, st)
          | _ => INR (InvalidCompletion "bad stored byte sequence")) of
      INR c => (INR c, st)
    | INL (n, st1) =>
        if 2 ** 64 ≤ n then (INR (PanicCompletion 65), st1) else
        case storage_byte_length st1.world.accounts addr slot of
          INR c => (INR c, st1)
        | INL old =>
            if static then (INR (InvalidCompletion "byte copy in static frame"), st1) else
            let st2 = scratch_write (if 32 ≤ n ∨ 32 ≤ old then SOME slot else NONE) st1;
                (bs, st3) =
                  (case v of
                     ReferenceValue (MemoryReference p _) =>
                       let (ws, st3) = memory_read (p + 32) (32 * ((n + 31) DIV 32)) st2 in
                       (TAKE n ws, st3)
                   | ScalarValue (BytesValue bs) => (bs, st2)
                   | _ => ([], st2)) in
            case replace_storage_bytes st3.world.accounts addr slot bs F of
              INL accounts => (INL (), st3 with world := st3.world with accounts := accounts)
            | INR c => (INR c, st3)
End

(* A byte copy into storage; one from the slot it targets changes nothing,
 * since the compiler's copy returns before it writes or uses its scratch. *)
Definition copy_byte_contents_def:
  copy_byte_contents src dst st =
    case dst of
      StorageReference PersistentStorage dst_addr dst_slot dst_offset dst_ty _ =>
        (case src of
           StorageReference PersistentStorage src_addr src_slot _ _ _ =>
             if src_addr = dst_addr ∧ src_slot = dst_slot then (INL (), st) else
             (case copy_storage_bytes st.world.accounts src dst st.frame.static_context of
                INL accounts =>
                  let accounts0 = st.world.accounts in
                  (INL (), scratch_write
                    (if IS_SOME (long_bytes_scratch accounts0 src_addr src_slot)
                     then SOME dst_slot
                     else long_bytes_scratch accounts0 dst_addr dst_slot)
                    (st with world := st.world with accounts := accounts))
              | INR c => (INR c, st))
         | _ =>
             if dst_offset ≠ 0 ∨ ¬byte_sequence_type dst_ty then
               (INR (InvalidCompletion "not storage bytes"), st)
             else
             case src of
               MemoryReference _ _ =>
                 copy_bytes_to_storage dst_addr dst_slot (ReferenceValue src)
                   st.frame.static_context st
             | _ =>
                 case byte_contents st src of
                   INR c => (INR c, st)
                 | INL (bs, st1) =>
                     copy_bytes_to_storage dst_addr dst_slot (ScalarValue (BytesValue bs))
                       st.frame.static_context st1)
    | _ => (INR (InvalidCompletion "bad storage byte copy"), st)
End

(* The length of an aggregate copy's source: a memory array's length word (a
 * static one's is its type's), or the number of values a calldata or storage
 * source gave. *)
Definition source_length_def:
  source_length ty v st =
    case v of
      ReferenceValue (MemoryReference p _) =>
        let (n, st1) = memory_length ty p st in (INL n, st1)
    | TupleValue vs => (INL (LENGTH vs), st)
    | _ => (INR (InvalidCompletion "bad stored array"), st)
End

(* Element or field i of an aggregate copy's source, of type ty: the word a
 * memory array or struct holds for it, or the value a calldata or storage
 * source gave. *)
Definition source_part_def:
  source_part env ty v (i : num) st =
    case v of
      ReferenceValue (MemoryReference p rty) =>
        read_memory_word env ty
          ((case rty of StructT _ => p | _ => memory_data rty p) + 32 * i) st
    | TupleValue vs =>
        (case DROP i vs of
           x :: _ => (INL x, st)
         | [] => (INR (InvalidCompletion "bad stored value"), st))
    | _ => (INR (InvalidCompletion "bad stored value"), st)
End

Definition store_storage_word_def:
  store_storage_word addr slot offset ty x (st : source_state) =
    case write_storage st.world.accounts addr slot offset ty x of
      SOME accounts => (INL (), st with world := st.world with accounts := accounts)
    | NONE => (INR (InvalidCompletion "bad storage write"), st)
End

(* Copy the value v of type src into storage at slot, of type dst, in one walk
 * that touches memory as the compiled copy does (copy_array_to_storage,
 * copy_struct_to_storage, copy_byte_array_to_storage). v is a memory object,
 * read word by word as the walk reaches it, or the value a calldata or
 * storage source gave, whose reads touch no memory. An array reads its length
 * (Panic(0x41) at 2^64 or more), resizes the stored array, clearing a shrunk
 * tail, hashes a dynamic array's slot in scratch word 0 (array_dataslot, even
 * when empty), then copies its elements in order, each completely before the
 * next one's word is read; a struct copies its fields the same way. Scalar
 * arrays write complete packed slots; retained structs overwrite members,
 * preserving scalar-slot padding and mappings. The state reached is returned
 * on a failure too. The fuel bounds the struct nesting. *)
Definition store_storage_value_def:
  (store_storage_value env (fuel : num) addr slot src dst v st =
    if (case v of
          ReferenceValue (MemoryReference _ rty) => rty ≠ src
        | _ => F)
    then (INR (InvalidCompletion "bad memory reference"), st)
    else if byte_sequence_type dst then copy_bytes_to_storage addr slot v F st
    else case (src, dst) of
      (ArrayT e _, ArrayT e' l) =>
        (case source_length src v st of
           (INR c, st1) => (INR c, st1)
         | (INL length, st1) =>
             if 2 ** 64 ≤ length then (INR (PanicCompletion 65), st1) else
             let accounts = st1.world.accounts in
             case storage_array_data accounts addr slot dst of
               (old_length, data) =>
                 if 2 ** 64 ≤ old_length then (INR FuelExhausted, st1) else
                 let accounts1 = if l = NONE then
                                   set_storage_word accounts addr slot (n2w length)
                                 else accounts in
                 let resized =
                   if is_stored_scalar_type e' then
                     (case fixed_storage_slots env
                             (ArrayT e' (SOME (MAX old_length length))) of
                        SOME slots => INL (clear_byte_slots slots accounts1 addr data, NONE)
                      | NONE => INL (accounts1, NONE))
                   else clear_storage_elements env (LENGTH env.type_declarations)
                          accounts1 addr data e' length (old_length - length) in
                 case resized of
                   INR c => (INR c, st1)
                 | INL (accounts2, _) =>
                     store_storage_elements env fuel addr data e e' v 0 length
                       (scratch_write (if l = NONE then SOME slot else NONE)
                          (st1 with world := st1.world with accounts := accounts2)))
    | (StructT _, StructT s) =>
        (case (lookup_struct env s, lookup_struct_layout env s) of
           (SOME fields, SOME layout) =>
             if fuel = 0 then (INR (InvalidCompletion "struct nesting"), st) else
             store_storage_fields env (fuel - 1) addr slot layout.struct_fields
               fields v 0 st
         | _ => (INR (InvalidCompletion "missing struct layout"), st))
    | _ => (INR (InvalidCompletion "bad stored array"), st)) ∧
  (store_storage_elements env fuel addr data src dst v i n st =
    if n = 0 then (INL (), st) else
    case storage_element_location env data dst i of
      NONE => (INR (InvalidCompletion "bad array element type"), st)
    | SOME (s, offset) =>
        case source_part env src v i st of
          (INR c, st1) => (INR c, st1)
        | (INL x, st1) =>
            case (if is_stored_scalar_type dst then
                    (case x of
                       ScalarValue y =>
                         (case eval_conversion env src dst y of
                            ScalarOk z => store_storage_word addr s offset dst z st1
                          | _ => (INR (InvalidCompletion "bad element conversion"), st1))
                     | _ => (INR (InvalidCompletion "bad stored element"), st1))
                  else store_storage_value env fuel addr s src dst x st1) of
              (INR c, st2) => (INR c, st2)
            | (INL _, st2) =>
                store_storage_elements env fuel addr data src dst v (i + 1) (n - 1) st2) ∧
  (store_storage_fields env fuel addr slot layout [] v j st = (INL (), st)) ∧
  (store_storage_fields env fuel addr slot layout ((f, ty) :: fields) v j st =
    case ALOOKUP (MAP (λm. (m.state_id, m)) layout) f of
      NONE => (INR (InvalidCompletion "missing field layout"), st)
    | SOME l =>
        case source_part env ty v j st of
          (INR c, st1) => (INR c, st1)
        | (INL x, st1) =>
            let s = slot + l.state_slot in
            case (if is_stored_scalar_type ty then
                    (case x of
                       ScalarValue y => store_storage_word addr s l.state_offset ty y st1
                     | _ => (INR (InvalidCompletion "bad stored field"), st1))
                  else case ty of
                    MappingT _ _ => (INL (), st1)
                  | _ => store_storage_value env fuel addr s ty ty x st1) of
              (INR c, st2) => (INR c, st2)
            | (INL _, st2) =>
                store_storage_fields env fuel addr slot layout fields v (j + 1) st2)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (env, fuel, addr, slot, src, dst, v, st) => (fuel, sol_type_size dst, 0n)
  | INR (INL (env, fuel, addr, data, src, dst, v, i, n, st)) =>
      (fuel, sol_type_size dst, n + 1)
  | INR (INR (env, fuel, addr, slot, layout, fields, v, j, st)) =>
      (fuel, list_size (sol_type_size o SND) fields, 1))’ >>
  rw[solidityASTTheory.sol_type_size_def, listTheory.list_size_def]
End

(* Copy the value v of type src into the storage reference dst. *)
Definition copy_to_storage_def:
  copy_to_storage env src v dst static st =
    case dst of
      StorageReference PersistentStorage addr slot 0 ty _ =>
        if static then (INR (InvalidCompletion "array copy in static frame"), st) else
        store_storage_value env (LENGTH env.type_declarations) addr slot src ty v st
    | _ => (INR (InvalidCompletion "bad storage array reference"), st)
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
val () = cv_auto_trans decode_reads_def;
val () = cv_auto_trans decode_bound_def;
val () = cv_auto_trans decode_reads_free_pointer_def;
val () = cv_auto_trans copy_bytes_to_storage_def;
val () = cv_auto_trans copy_byte_contents_def;
val () = cv_auto_trans source_length_def;
val () = cv_auto_trans source_part_def;
val () = cv_auto_trans store_storage_word_def;

val store_storage_value_pre_def = cv_auto_trans_pre_rec
  "store_storage_value_pre store_storage_elements_pre store_storage_fields_pre"
  store_storage_value_def (
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (env, fuel, addr, slot, src, dst, v, st) => (cv$c2n fuel, cv_size dst, 0)
  | INR (INL (env, fuel, addr, data, src, dst, v, i, n, st)) =>
      (cv$c2n fuel, cv_size dst, cv$c2n n + 1)
  | INR (INR (env, fuel, addr, slot, layout, fields, v, j, st)) =>
      (cv$c2n fuel, cv_size fields, 1))’ >>
  cv_termination_tac
);

Theorem store_storage_value_pre[cv_pre]:
  (∀env fuel addr slot src dst v st.
     store_storage_value_pre env fuel addr slot src dst v st) ∧
  (∀env fuel addr data src dst v i n st.
     store_storage_elements_pre env fuel addr data src dst v i n st) ∧
  (∀env fuel addr slot layout fields v j st.
     store_storage_fields_pre env fuel addr slot layout fields v j st)
Proof
  ho_match_mp_tac store_storage_value_ind >> rpt strip_tac >>
  simp[Once store_storage_value_pre_def] >> rw[] >> gvs[] >>
  (* the precondition holds the resized state as a record literal *)
  qmatch_goalsub_abbrev_tac ‘scratch_write _ s3’ >>
  qmatch_asmsub_abbrev_tac ‘scratch_write _ s2’ >>
  ‘s3 = s2’ by (
    unabbrev_all_tac >>
    rename1 ‘storage_array_data s1.world.accounts’ >> Cases_on ‘s1’ >>
    rename1 ‘source_state w’ >> Cases_on ‘w’ >>
    simp[solidityStateTheory.source_state_component_equality,
         solidityStateTheory.source_world_component_equality]) >>
  gvs[]
QED

val () = cv_auto_trans copy_to_storage_def;
val () = cv_auto_trans convert_byte_reference_def;
