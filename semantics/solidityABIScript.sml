(* The ABI at the contract boundary, for every ABI type (scalars, byte
 * sequences, arrays and structs) wherever its value is: calldata arguments,
 * return data, abi.encode and abi.decode, revert data and event logs, over
 * Verifereum's contractABI encoding.
 *)
Theory solidityABI
Ancestors
  contractABI
  (* for its cv encodings of runtime values and events, so that every
   * descendant sees one encoding *)
  solidityMemory
Libs
  cv_transLib wordsLib intLib

(* The ABI type of ty, each struct the tuple of its fields' types. The fuel
 * bounds the struct nesting; callers pass the number of type declarations,
 * which a struct the ABI admits nests within. *)
Definition abi_type_def:
  (abi_type env (fuel : num) ty =
    case ty of
      UintT n => Uint n
    | IntT n => Int n
    | BoolT => Bool
    | AddressT _ => Address
    | FixedBytesT n => Bytes (SOME n)
    | EnumT _ => Uint 8
    | BytesT => Bytes NONE
    | StringT => String
    | ArrayT element length => Array length (abi_type env fuel element)
    | StructT s =>
        (case lookup_struct env s of
           SOME fields =>
             if fuel = 0 then Tuple []
             else Tuple (abi_types env (fuel - 1) (MAP SND fields))
         | NONE => Tuple [])
    | LocatedT _ ty' => abi_type env fuel ty'
    | _ => Tuple []) ∧
  (abi_types env fuel [] = []) ∧
  (abi_types env fuel (ty :: tys) = abi_type env fuel ty :: abi_types env fuel tys)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    INL (env, fuel, ty) => (fuel, sol_type_size ty)
  | INR (env, fuel, tys) => (fuel, list_size sol_type_size tys))’ >>
  rw[solidityASTTheory.sol_type_size_def, listTheory.list_size_def]
End

Definition abi_value_def:
  (abi_value (UintT _) (ScalarValue (IntegerValue i)) = SOME (NumV (Num i))) ∧
  (abi_value (IntT _) (ScalarValue (IntegerValue i)) = SOME (IntV i)) ∧
  (abi_value BoolT (ScalarValue (BoolValue b)) =
    SOME (NumV (if b then 1 else 0))) ∧
  (abi_value (AddressT _) (ScalarValue (AddressValue a)) =
    SOME (NumV (w2n a))) ∧
  (abi_value (FixedBytesT _) (ScalarValue (BytesValue bs)) = SOME (BytesV bs)) ∧
  (abi_value (EnumT _) (ScalarValue (IntegerValue i)) = SOME (NumV (Num i))) ∧
  (abi_value BytesT (ScalarValue (BytesValue bs)) = SOME (BytesV bs)) ∧
  (abi_value StringT (ScalarValue (BytesValue bs)) = SOME (BytesV bs)) ∧
  (abi_value (LocatedT _ ty) v = abi_value ty v) ∧
  (abi_value _ _ = NONE)
End

(* The ABI value of a value tree: an array's elements or a struct's fields in
 * order, as a list. *)
Definition value_abi_value_def:
  (value_abi_value env ty v =
    case (ty, v) of
      (ArrayT element _, TupleValue vs) =>
        OPTION_MAP ListV (values_abi_value env element vs)
    | (ArrayT _ _, _) => NONE
    | (StructT s, TupleValue vs) =>
        (case lookup_struct env s of
           SOME fields => OPTION_MAP ListV (fields_abi_value env (MAP SND fields) vs)
         | NONE => NONE)
    | (StructT _, _) => NONE
    | _ => abi_value ty v) ∧
  (values_abi_value env element [] = SOME []) ∧
  (values_abi_value env element (v :: vs) =
    case (value_abi_value env element v, values_abi_value env element vs) of
      (SOME a, SOME as) => SOME (a :: as)
    | _ => NONE) ∧
  (fields_abi_value env [] [] = SOME []) ∧
  (fields_abi_value env (ty :: tys) (v :: vs) =
    case (value_abi_value env ty v, fields_abi_value env tys vs) of
      (SOME a, SOME as) => SOME (a :: as)
    | _ => NONE) ∧
  (fields_abi_value env _ _ = NONE)
Termination
  WF_REL_TAC ‘measure (λx. case x of
    INL (env, ty, v) => runtime_value_size v
  | INR (INL (env, element, vs)) => list_size runtime_value_size vs
  | INR (INR (env, tys, vs)) => list_size runtime_value_size vs)’ >>
  rw[solidityCoreTheory.runtime_value_size_def, listTheory.list_size_def]
End

(* Zero bytes the compiler's encoder writes past the end of an encoding of a
 * value not in storage (a stored one gives its own, storage_abi_value). A
 * byte sequence copied from memory or calldata is followed by a cleared
 * word; a literal writes whole words. Only the encoding's last dynamic part,
 * recursively, can spill past its end. *)
Datatype:
  encoding_source = CopiedBytes | StoredBytes | LiteralBytes
End

Definition encoding_source_def:
  encoding_source v =
    case v of
      ReferenceValue (StorageReference _ _ _ _ _ _) => StoredBytes
    | ReferenceValue _ => CopiedBytes
    | _ => LiteralBytes
End

Definition padded_bytes_spill_def:
  padded_bytes_spill src (l : num) =
    case src of
      CopiedBytes => if l MOD 32 = 0 then 32 else l MOD 32
    | StoredBytes => if l = 0 then 32 else 0
    | LiteralBytes => 0
End

(* The last dynamic part's spill, NONE when no part is dynamic. *)
Definition later_spill_def:
  later_spill t n rest =
    case rest of
      SOME m => SOME m
    | NONE => if is_dynamic t then SOME n else NONE
End

Definition abi_spill_def:
  (abi_spill src (Bytes NONE) (BytesV bs) = padded_bytes_spill src (LENGTH bs)) ∧
  (abi_spill src String (BytesV bs) = padded_bytes_spill src (LENGTH bs)) ∧
  (abi_spill src (Array _ t) (ListV vs) =
    (case parts_spill src (REPLICATE (LENGTH vs) t) vs of SOME n => n | NONE => 0)) ∧
  (abi_spill src (Tuple ts) (ListV vs) = (case parts_spill src ts vs of SOME n => n | NONE => 0)) ∧
  (abi_spill src _ _ = 0) ∧
  (parts_spill src (t :: ts) (v :: vs) =
    later_spill t (abi_spill src t v) (parts_spill src ts vs)) ∧
  (parts_spill src _ _ = NONE)
Termination
  WF_REL_TAC ‘measure (λx. case x of
    INL (src, t, v) => abi_value_size v
  | INR (src, ts, vs) => list_size abi_value_size vs)’ >>
  rw[contractABITheory.abi_value_size_def, listTheory.list_size_def]
End

(* What the compiled encoder has written of a value when reading one of its
 * parts ends the frame: it writes in place and reads each part only when it
 * reaches it. Nothing, when the value's own read failed; else a dynamic
 * array's length (written first), the parts it completed (each its ABI
 * value, encoding and spill), whether the failing part's offset word is
 * written before the part is read (a calldata struct field's is written only
 * after its offset is validated), and what it wrote of the failing part. *)
Datatype:
  abi_partial =
    PartialNone
  | PartialParts (num option) ((abi_value # byte list # byte list) list) bool abi_partial
End

(* A completed part read as the value tree v of type ty from memory or
 * calldata: its ABI value, encoding and spill. *)
Definition tree_part_def:
  tree_part env ty v =
    let t = abi_type env (LENGTH env.type_declarations) ty in
    OPTION_MAP (λa. (a, enc t a, REPLICATE (abi_spill CopiedBytes t a) (0w : word8)))
      (value_abi_value env ty v)
End

Definition shift_writes_def:
  shift_writes (n : num) (ws : (num # byte list) list) = MAP (λ(off, bs). (n + off, bs)) ws
End

(* The ABI types of the parts of a value of ABI type t, given a dynamic
 * array's length; an array's only up to its kth, since its length comes
 * from its input and a partial needs the parts up to its failing one. *)
Definition component_types_def:
  component_types t len (k : num) =
    case t of
      Tuple ts => ts
    | Array (SOME n) e => REPLICATE (MIN n k) e
    | Array NONE e => REPLICATE (MIN (case len of SOME n => n | NONE => 0) k) e
    | _ => []
End

(* The length of the heads of the parts of a value of ABI type t, given a
 * dynamic array's length: head_lengths of all its component types, without
 * listing an array's elements. *)
Definition parts_head_length_def:
  parts_head_length t len =
    case t of
      Tuple ts => head_lengths ts 0
    | Array (SOME n) e => n * (if is_dynamic e then 32 else static_length e)
    | Array NONE e =>
        (case len of SOME n => n | NONE => 0) *
        (if is_dynamic e then 32 else static_length e)
    | _ => 0
End

(* The writes, relative to the start of the value's encoding, of a partial in
 * the standard head/tail layout: each completed part its head (its encoding
 * when static, else its offset word) and a dynamic one its tail with its
 * spill, which a later write may overwrite; then the failing part, its
 * offset word written when it was written before the read or the part wrote
 * anything. *)
Definition partial_writes_def:
  (partial_writes t PartialNone = [] : (num # byte list) list) ∧
  (partial_writes t (PartialParts len done w q) =
    let ts = component_types t len (SUC (LENGTH done)) in
    let hl = parts_head_length t len in
    case len of
      SOME n =>
        (0, enc (Uint 256) (NumV n)) ::
        shift_writes 32 (parts_writes hl 0 0 ts done w q)
    | NONE => parts_writes hl 0 0 ts done w q) ∧
  (parts_writes hl h tl [] done w q = []) ∧
  (parts_writes hl h tl (t :: ts) done w q =
    case done of
      (a, part_bs, sp) :: rest =>
        if is_dynamic t then
          (h, enc (Uint 256) (NumV (hl + tl))) :: (hl + tl, part_bs ++ sp) ::
          parts_writes hl (h + 32) (tl + LENGTH part_bs) ts rest w q
        else (h, part_bs) :: parts_writes hl (h + LENGTH part_bs) tl ts rest w q
    | [] =>
        if is_dynamic t then
          (case (w, q) of
             (F, PartialNone) => []
           | _ => [(h, enc (Uint 256) (NumV (hl + tl)))]) ++
          shift_writes (hl + tl) (partial_writes t q)
        else shift_writes h (partial_writes t q))
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    INL (t, p) => (abi_partial_size p, 0n)
  | INR (hl, h, tl, ts, done, w, q) => (abi_partial_size q, LENGTH ts + 1))’ >>
  rw[]
End

(* A value's partial writes, laid out from start. *)
Definition apply_writes_def:
  (apply_writes (start : num) [] (st : source_state) = st) ∧
  (apply_writes start ((off, bs) :: ws) st =
    apply_writes start ws (memory_write (start + off) bs st))
End

(* The value of a memory array or struct, as the encoder reads it: the tuple
 * of its elements or fields, byte sequences as their bytes; on a failed read,
 * what the encoder has written of it (abi_partial: it writes a part's offset
 * word after reading the part's pointer, which cannot fail). Also how far the
 * reads reach, raised from reach (touched_reach), on a failed read too. The
 * fuel bounds the struct nesting. *)
Definition memory_value_def:
  (memory_value env (fuel : num) ty v reach st =
    case (ty, v) of
      (ArrayT element length, ReferenceValue (MemoryReference p rty)) =>
        if rty ≠ ty then
          (INR (InvalidCompletion "bad memory array reference", PartialNone), reach, st) else
        let (n, st1) = memory_length ty p st in
        let reach1 = (case length of NONE => touched_reach reach p 32 | SOME _ => reach) in
        let (r, reach2, st2) =
          memory_elements env fuel element (memory_data ty p) n reach1 st1 in
        ((case r of
            INL vs => INL (TupleValue vs)
          | INR (c, done, wr, q) =>
              INR (c, PartialParts (if length = NONE then SOME n else NONE) done wr q)),
         reach2, st2)
    | (StructT s, ReferenceValue (MemoryReference p rty)) =>
        if rty ≠ ty then
          (INR (InvalidCompletion "bad memory struct reference", PartialNone), reach, st) else
        (case lookup_struct env s of
           SOME fields =>
             if fuel = 0 then (INR (InvalidCompletion "struct nesting", PartialNone), reach, st) else
             let (r, reach1, st1) =
               memory_fields env (fuel - 1) (MAP SND fields) p reach st in
             ((case r of
                 INL vs => INL (TupleValue vs)
               | INR (c, done, wr, q) => INR (c, PartialParts NONE done wr q)), reach1, st1)
         | NONE => (INR (InvalidCompletion "unknown struct", PartialNone), reach, st))
    | (_, ReferenceValue (MemoryReference p rty)) =>
        if byte_sequence_type rty then
          let (bs, st1) = memory_bytes p st in
          (INL (ScalarValue (BytesValue bs)),
           touched_reach (touched_reach reach p 32) (p + 32) (LENGTH bs), st1)
        else (INR (InvalidCompletion "bad memory value", PartialNone), reach, st)
    | (_, ScalarValue _) => (INL v, reach, st)
    | _ => (INR (InvalidCompletion "bad memory value", PartialNone), reach, st)) ∧
  (memory_elements env fuel element p n reach st =
    if n = 0 then (INL [], reach, st) else
    let reach1 = touched_reach reach p 32 in
    case read_memory_word env element p st of
      (INR c, st1) => (INR (c, [], T, PartialNone), reach1, st1)
    | (INL x, st1) =>
        case memory_value env fuel element x reach1 st1 of
          (INR (c, q), reach2, st2) => (INR (c, [], T, q), reach2, st2)
        | (INL v, reach2, st2) =>
            let (r, reach3, st3) =
              memory_elements env fuel element (p + 32) (n - 1) reach2 st2 in
            ((case r of
                INL vs => INL (v :: vs)
              | INR (c, done, wr, q) =>
                  (case tree_part env element v of
                     SOME done1 => INR (c, done1 :: done, wr, q)
                   | NONE => INR (InvalidCompletion "bad ABI value", [], T, PartialNone))),
             reach3, st3)) ∧
  (memory_fields env fuel [] p reach st = (INL [], reach, st)) ∧
  (memory_fields env fuel (ty :: tys) p reach st =
    let reach1 = touched_reach reach p 32 in
    case read_memory_word env ty p st of
      (INR c, st1) => (INR (c, [], T, PartialNone), reach1, st1)
    | (INL x, st1) =>
        case memory_value env fuel ty x reach1 st1 of
          (INR (c, q), reach2, st2) => (INR (c, [], T, q), reach2, st2)
        | (INL v, reach2, st2) =>
            let (r, reach3, st3) =
              memory_fields env fuel tys (p + 32) reach2 st2 in
            ((case r of
                INL vs => INL (v :: vs)
              | INR (c, done, wr, q) =>
                  (case tree_part env ty v of
                     SOME done1 => INR (c, done1 :: done, wr, q)
                   | NONE => INR (InvalidCompletion "bad ABI value", [], T, PartialNone))),
             reach3, st3))
Termination
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (env, fuel, ty, v, reach, st) => (fuel, sol_type_size ty, 0n)
  | INR (INL (env, fuel, element, p, n, reach, st)) =>
      (fuel, sol_type_size element, n + 1)
  | INR (INR (env, fuel, tys, p, reach, st)) =>
      (fuel, list_size sol_type_size tys, 1))’ >>
  rw[solidityASTTheory.sol_type_size_def, listTheory.list_size_def] >>
  qpat_x_assum ‘(_, _) = _’ (assume_tac o SYM) >> gvs[]
End

(* Inverse of abi_value on values valid_enc accepts. *)
Definition abi_runtime_value_def:
  (abi_runtime_value (UintT _) (NumV n) = SOME (ScalarValue (IntegerValue (&n)))) ∧
  (abi_runtime_value (IntT _) (IntV i) = SOME (ScalarValue (IntegerValue i))) ∧
  (abi_runtime_value BoolT (NumV n) = SOME (ScalarValue (BoolValue (n = 1)))) ∧
  (abi_runtime_value (AddressT _) (NumV n) =
    SOME (ScalarValue (AddressValue (n2w n)))) ∧
  (abi_runtime_value (FixedBytesT _) (BytesV bs) =
    SOME (ScalarValue (BytesValue bs))) ∧
  (* a uint8, which dispatch checks against the enum's members *)
  (abi_runtime_value (EnumT _) (NumV n) = SOME (ScalarValue (IntegerValue (&n)))) ∧
  (abi_runtime_value _ _ = NONE)
End

Definition abi_word_def:
  abi_word bs pos = num_of_be_bytes (TAKE 32 (DROP pos bs))
End

(* n bytes of an input at pos, reading zeros past the bytes held. *)
Definition input_bytes_def:
  input_bytes (bs : word8 list) pos n =
    let xs = TAKE n (DROP pos bs) in xs ++ REPLICATE (n - LENGTH xs) 0w
End

Definition input_word_def:
  input_word bs pos = num_of_be_bytes (input_bytes bs pos 32)
End

(* The bytes an element or field takes in the head of its array or struct. *)
Definition abi_stride_def:
  abi_stride env ty =
    let a = abi_type env (LENGTH env.type_declarations) ty in
    if is_dynamic a then 32 else static_length a
End

(* The bytes the heads of a value of ABI type a take: a tuple's or fixed
 * array's components' heads, else a word. A dynamic struct or fixed array in
 * calldata needs this much calldata where it starts. *)
Definition abi_head_size_def:
  abi_head_size a =
    case a of
      Tuple ts => head_lengths ts 0
    | Array (SOME n) t => head_lengths (REPLICATE n t) 0
    | _ => 32
End

(* The length a calldata reference to a value of type ty records: a fixed
 * array's length, else 0; a dynamic array's comes from the calldata. *)
Definition calldata_length_def:
  calldata_length ty = case ty of ArrayT _ (SOME n) => n | _ => 0
End

(* The calldata word at pos, zero past the end, as CALLDATALOAD reads it. *)
Definition calldata_word_def:
  calldata_word (cd : byte list) pos =
    num_of_be_bytes (TAKE 32 (DROP pos cd ++ REPLICATE 32 0w))
End

(* The calldata position an offset at ptr, relative to base, leads to, as the
 * pinned compiler's calldata accessors check it: the offset, a signed word, is
 * below the calldata left after base less needed - 1, needed being the bytes
 * the value's head or length word takes. Addresses wrap at 2^256. *)
Definition calldata_offset_def:
  calldata_offset cd base ptr needed =
    let size : 256 word = n2w (LENGTH cd) in
    let rel : 256 word = n2w (calldata_word cd ptr) in
    if rel < size - n2w base - n2w (needed - 1) then SOME (n2w base + rel : 256 word)
    else NONE
End

(* A byte sequence or dynamic array in calldata, reached through the offset
 * at ptr: its length there is below 2^64, and its data of stride bytes per
 * element ends within the calldata, compared as signed words. The data's
 * position and the length. *)
Definition calldata_tail_def:
  calldata_tail cd base ptr stride =
    case calldata_offset cd base ptr 32 of
      NONE => INR (RevertCompletion [])
    | SOME addr =>
      let size : 256 word = n2w (LENGTH cd) in
      let length = calldata_word cd (w2n addr) in
      if 2 ** 64 ≤ length then INR (RevertCompletion []) else
      let data = addr + 32w in
      if size - n2w (length * stride) < data then INR (RevertCompletion [])
      else INL (w2n data, length)
End

(* The element or field of a calldata array or struct whose head is at head,
 * as the pinned compiler's calldata accessors read it: a scalar read and
 * validated in place (an enum outside its members reverts), a static array or
 * struct in place, and any other value through the offset there, relative to
 * base, the start of the array's data or of the struct. *)
Definition calldata_part_def:
  calldata_part env cd ty base head =
    let a = abi_type env (LENGTH env.type_declarations) ty in
    if is_stored_scalar_type ty then
      let word = TAKE 32 (DROP head cd ++ REPLICATE 32 0w) in
      if ¬valid_enc a word then INR (RevertCompletion []) else
      (case abi_runtime_value ty (dec a word) of
         SOME (ScalarValue v) =>
           if (case ty of EnumT _ => ¬scalar_has_type env ty v | _ => F) then
             INR (RevertCompletion [])
           else INL (ScalarValue v)
       | _ => INR (InvalidCompletion "bad calldata element type"))
    else if ¬is_dynamic a then
      INL (ReferenceValue (CalldataReference head (calldata_length ty) ty))
    else if byte_sequence_type ty ∨ (case ty of ArrayT _ NONE => T | _ => F) then
      let stride = case ty of ArrayT inner NONE => abi_stride env inner | _ => 1 in
      (case calldata_tail cd base head stride of
         INL (pos, length) => INL (ReferenceValue (CalldataReference pos length ty))
       | INR c => INR c)
    else
      case calldata_offset cd base head (abi_head_size a) of
        SOME addr =>
          INL (ReferenceValue (CalldataReference (w2n addr) (calldata_length ty) ty))
      | NONE => INR (RevertCompletion [])
End

(* Field f of the calldata struct of type s at pos: a scalar field as a
 * reference to its head, read and validated when the field is read; any other
 * field as calldata_part reaches it. *)
Definition calldata_struct_field_def:
  calldata_struct_field env cd s pos f =
    case lookup_struct env s of
      NONE => INR (InvalidCompletion "unknown struct")
    | SOME fields =>
      case field_position f fields of
        NONE => INR (InvalidCompletion "unknown struct field")
      | SOME (k, ty) =>
        let head = pos + head_lengths (abi_types env (LENGTH env.type_declarations)
                                         (TAKE k (MAP SND fields))) 0 in
        if is_stored_scalar_type ty then
          INL (ReferenceValue (CalldataReference head 0 ty))
        else calldata_part env cd ty pos head
End

(* The value of a calldata array, struct or byte sequence at data, read part
 * by part through the pinned compiler's calldata accessors, so an invalid
 * element or offset reverts: an array or struct as the tuple of its elements
 * or fields, a byte sequence as its bytes; on a failed read, what the encoder
 * has written of it (abi_partial). The encoder writes an array element's
 * offset word before reading the element, and a struct field's only after
 * reading the field's offset. The encoder and the copies to storage read
 * calldata this way. The fuel bounds the struct nesting. *)
Definition calldata_value_def:
  (calldata_value env (fuel : num) cd ty data length =
    case ty of
      ArrayT element l =>
        (case calldata_values env fuel cd element data 0 length of
           INL vs => INL (TupleValue vs)
         | INR (c, done, w, q) =>
             INR (c, PartialParts (if l = NONE then SOME length else NONE) done w q))
    | StructT s =>
        (case lookup_struct env s of
           SOME fields =>
             if fuel = 0 then INR (InvalidCompletion "struct nesting", PartialNone) else
             (case calldata_fields env (fuel - 1) cd (MAP SND fields) data data of
                INL vs => INL (TupleValue vs)
              | INR (c, done, w, q) => INR (c, PartialParts NONE done w q))
         | NONE => INR (InvalidCompletion "unknown struct", PartialNone))
    | _ => INL (ScalarValue (BytesValue
             (TAKE length (DROP data cd ++ REPLICATE length 0w))))) ∧
  (calldata_values env fuel cd element data i n =
    if n = 0 then INL [] else
    case calldata_part_value env fuel cd element data
           (data + i * abi_stride env element) of
      INR (c, q) => INR (c, [], T, q)
    | INL v =>
        case calldata_values env fuel cd element data (i + 1) (n - 1) of
          INL vs => INL (v :: vs)
        | INR (c, done, w, q) =>
            (case tree_part env element v of
               SOME done1 => INR (c, done1 :: done, w, q)
             | NONE => INR (InvalidCompletion "bad ABI value", [], T, PartialNone))) ∧
  (calldata_fields env fuel cd [] base head = INL []) ∧
  (calldata_fields env fuel cd (ty :: tys) base head =
    case calldata_part_value env fuel cd ty base head of
      INR (c, q) => INR (c, [], F, q)
    | INL v =>
        case calldata_fields env fuel cd tys base (head + abi_stride env ty) of
          INL vs => INL (v :: vs)
        | INR (c, done, w, q) =>
            (case tree_part env ty v of
               SOME done1 => INR (c, done1 :: done, w, q)
             | NONE => INR (InvalidCompletion "bad ABI value", [], T, PartialNone))) ∧
  (calldata_part_value env fuel cd ty base head =
    case calldata_part env cd ty base head of
      INL (ReferenceValue (CalldataReference pos length _)) =>
        calldata_value env fuel cd ty pos length
    | INL v => INL v
    | INR c => INR (c, PartialNone))
Termination
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (_, fuel, _, ty, _, _) => (fuel, sol_type_size ty, 0)
  | INR (INL (_, fuel, _, element, _, _, n)) => (fuel, sol_type_size element, n + 2)
  | INR (INR (INL (_, fuel, _, tys, _, _))) => (fuel, list_size sol_type_size tys, 0)
  | INR (INR (INR (_, fuel, _, ty, _, _))) => (fuel, sol_type_size ty, 1))’ >>
  rw[solidityASTTheory.sol_type_size_def, listTheory.list_size_def]
End

(* The tuple head/tail layout, using already encoded component bodies. *)
Definition encoded_abi_parts_def:
  (encoded_abi_parts hl tl [] = ([], [])) ∧
  (encoded_abi_parts hl tl ((ty, encoded_body) :: parts) =
    let dynamic = is_dynamic ty in
    let tail = if dynamic then encoded_body else [] in
    let head = if dynamic then enc (Uint 256) (NumV (hl + tl)) else encoded_body in
    let (heads, tails) = encoded_abi_parts hl (tl + LENGTH tail) parts in
    (head ++ heads, tail ++ tails))
End

Definition encoded_abi_tuple_def:
  encoded_abi_tuple parts =
    let (heads, tails) = encoded_abi_parts (head_lengths (MAP FST parts) 0) 0 parts in
    heads ++ tails
End

(* The bytes an encoding's last dynamic part writes past its end, given each
 * part's ABI type and those bytes: none when no part is dynamic. *)
Definition last_spill_def:
  (last_spill ([] : (abi_type # byte list) list) = []) ∧
  (last_spill ((t, sp) :: ps) =
    if EXISTS (λ(t, sp). is_dynamic t) ps then last_spill ps
    else if is_dynamic t then sp else [])
End

(* A storage value encoded in place, as the pinned encoder does: its ABI
 * value, its encoding, and the bytes written past its end; on a failed read,
 * what the encoder has written of it (abi_partial). Also the data slot it
 * last hashed in scratch, failed reads included (as read_scratch on success).
 * Scalars are read cleaned; a byte sequence copies whole data words, keeping
 * unused dirty bytes, except the length byte of a short one
 * (storage_byte_data), and an empty one still writes its slot's word past
 * its end. A length of 2^64 or more is unsupported: the compiled encoder has
 * no length check, so it does not panic with 0x41, and what it does instead
 * (run out of gas, or panic cleaning an element) the source does not track.
 * The fuel bounds the struct nesting. *)
Definition storage_abi_value_def:
  (storage_abi_value env (fuel : num) accounts addr slot ty =
    if byte_sequence_type ty then
      (case storage_byte_length accounts addr slot of
         INR c => (INR (c, PartialNone), NONE)
       | INL length =>
         if 2 ** 64 ≤ length then
           (INR (InvalidCompletion
                   "unsupported: a stored sequence of 2^64 or more elements encoded to memory",
                 PartialNone), NONE) else
         let w = if 32 ≤ length then SOME slot else NONE in
         let data = storage_byte_data accounts addr slot length in
         case abi_value ty (ScalarValue (BytesValue (TAKE length data))) of
           SOME a =>
             if length = 0 then (INL (a, enc (Uint 256) (NumV 0), data), w)
             else (INL (a, enc (Uint 256) (NumV length) ++ data, []), w)
         | NONE => (INR (InvalidCompletion "bad ABI value", PartialNone), w))
    else case ty of
      ArrayT element l =>
        (case storage_array_data accounts addr slot ty of
           (length, data) =>
             if 2 ** 64 ≤ length then
               (INR (InvalidCompletion
                       "unsupported: a stored sequence of 2^64 or more elements encoded to memory",
                     PartialNone), NONE) else
             let (r, w) = storage_abi_elements env fuel accounts addr data element 0 length in
             let w1 = later_scratch (if l = NONE then SOME slot else NONE) w in
             case r of
               INL parts =>
                 let t = abi_type env (LENGTH env.type_declarations) element in
                 (INL (ListV (MAP FST parts),
                       (if l = NONE then enc (Uint 256) (NumV length) else []) ++
                       encoded_abi_tuple (MAP (λ(a, bs, sp). (t, bs)) parts),
                       last_spill (MAP (λ(a, bs, sp). (t, sp)) parts)), w1)
             | INR (c, done, q) =>
                 (INR (c, PartialParts (if l = NONE then SOME length else NONE) done T q), w1))
    | StructT s =>
        (case (lookup_struct env s, lookup_struct_layout env s) of
           (SOME fields, SOME layout) =>
             if fuel = 0 then (INR (InvalidCompletion "struct nesting", PartialNone), NONE) else
             (case storage_abi_fields env (fuel - 1) accounts addr slot
                     layout.struct_fields fields of
                (INL parts, w) =>
                  (INL (ListV (MAP FST parts),
                        encoded_abi_tuple (MAP (λ(a, (t, bs), sp). (t, bs)) parts),
                        last_spill (MAP (λ(a, (t, bs), sp). (t, sp)) parts)), w)
              | (INR (c, done, q), w) => (INR (c, PartialParts NONE done T q), w))
         | _ => (INR (InvalidCompletion "missing struct layout", PartialNone), NONE))
    | _ => (INR (InvalidCompletion "bad storage ABI type", PartialNone), NONE)) ∧
  (storage_abi_elements env fuel accounts addr data element i n =
    if n = 0 then (INL [], NONE) else
    case storage_element_location env data element i of
      NONE => (INR (InvalidCompletion "bad array element type", [], PartialNone), NONE)
    | SOME (s, offset) =>
        let (value, w) =
          if is_stored_scalar_type element then
            ((case read_storage env accounts addr s offset element of
                SOME v =>
                  (case abi_value element (ScalarValue v) of
                     SOME a => INL (a, enc (abi_type env 0 element) a, [])
                   | NONE => INR (InvalidCompletion "bad ABI value", PartialNone))
              | NONE => INR (InvalidCompletion "bad storage read", PartialNone)), NONE)
          else storage_abi_value env fuel accounts addr s element in
        case value of
          INR (c, q) => (INR (c, [], q), w)
        | INL entry =>
            let (r, w') = storage_abi_elements env fuel accounts addr data element (i + 1) (n - 1) in
            ((case r of
                INL entries => INL (entry :: entries)
              | INR (c, done, q) => INR (c, entry :: done, q)), later_scratch w w')) ∧
  (storage_abi_fields env fuel accounts addr slot layout [] = (INL [], NONE)) ∧
  (storage_abi_fields env fuel accounts addr slot layout ((f, ty) :: fields) =
    case ALOOKUP (MAP (λv. (v.state_id, v)) layout) f of
      NONE => (INR (InvalidCompletion "missing field layout", [], PartialNone), NONE)
    | SOME v =>
        let s = slot + v.state_slot in
        let (value, w) =
          if is_stored_scalar_type ty then
            ((case read_storage env accounts addr s v.state_offset ty of
                SOME x =>
                  (case abi_value ty (ScalarValue x) of
                     SOME a => INL (a, enc (abi_type env 0 ty) a, [])
                   | NONE => INR (InvalidCompletion "bad ABI value", PartialNone))
              | NONE => INR (InvalidCompletion "bad storage read", PartialNone)), NONE)
          else storage_abi_value env fuel accounts addr s ty in
        case value of
          INR (c, q) => (INR (c, [], q), w)
        | INL (a, encoded, sp) =>
            let (r, w') = storage_abi_fields env fuel accounts addr slot layout fields in
            ((case r of
                INL parts =>
                  INL ((a, (abi_type env (LENGTH env.type_declarations) ty, encoded), sp)
                       :: parts)
              | INR (c, done, q) => INR (c, (a, encoded, sp) :: done, q)), later_scratch w w'))
Termination
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (env, fuel, accounts, addr, slot, ty) => (fuel, sol_type_size ty, 0)
  | INR (INL (env, fuel, accounts, addr, data, element, i, n)) =>
      (fuel, sol_type_size element, n + 1)
  | INR (INR (env, fuel, accounts, addr, slot, layout, fields)) =>
      (fuel, list_size (sol_type_size o SND) fields, 1))’ >>
  rw[solidityASTTheory.sol_type_size_def, listTheory.list_size_def]
End

(* The value tree of a memory, calldata or storage array, struct or byte
 * sequence of type ty, as the encoder reads it, and how far its memory reads
 * reach, raised from reach (memory_value); a storage one's reach is its
 * scratch hash's. A copy to storage reads a calldata or storage source this
 * way too. Calldata
 * is read through the calldata accessors; a calldata array's own data span
 * was checked when it was decoded. *)
Definition array_copy_value_def:
  array_copy_value env reach (st : source_state) ty r =
    case r of
      MemoryReference _ _ =>
        memory_value env (LENGTH env.type_declarations) ty (ReferenceValue r) reach st
    | CalldataReference data n rty =>
        if rty ≠ ty then
          (INR (InvalidCompletion "bad calldata array reference", PartialNone), reach, st)
        else (calldata_value env (LENGTH env.type_declarations)
                st.frame.call_data ty data n, reach, st)
    | StorageReference PersistentStorage addr slot 0 rty _ =>
        if rty ≠ ty then
          (INR (InvalidCompletion "bad storage array reference", PartialNone), reach, st)
        else (case storage_array_value env (LENGTH env.type_declarations)
                     st.world.accounts addr slot ty of
                INL v =>
                  let w = read_scratch env (LENGTH env.type_declarations)
                            st.world.accounts addr slot ty in
                  (INL v, scratch_reach reach w, scratch_write w st)
              | INR c => (INR (c, PartialNone), reach, st))
    | _ => (INR (InvalidCompletion "bad array reference", PartialNone), reach, st)
End


(* abi.encodePacked, the concatenations and indexed topics write a byte
 * sequence v without padding, and these bytes past its contents bs: a copied
 * one is followed by a cleared word, a literal one fills its last word with
 * zeros, and a stored one is written in whole storage words
 * (storage_byte_data), which keep what its slots hold past its length. *)
Definition packed_bytes_tail_def:
  packed_bytes_tail accounts v (bs : byte list) =
    case v of
      ReferenceValue (StorageReference _ addr slot _ _ _) =>
        DROP (LENGTH bs) (storage_byte_data accounts addr slot (LENGTH bs))
    | ReferenceValue _ => REPLICATE 32 0w
    | _ => REPLICATE ((32 - LENGTH bs MOD 32) MOD 32) 0w
End

(* What a packed part writes past its end: a value its word's other bytes. *)
Definition packed_tail_def:
  packed_tail accounts ty v (bs : byte list) =
    case ty of
      LocatedT _ (ArrayT _ _) => []
    | LocatedT _ _ => packed_bytes_tail accounts v bs
    | _ => REPLICATE (32 - LENGTH bs) 0w : byte list
End

(* The length of v's in-place encoding (indexed_data): a byte sequence padded
 * to whole words, an array or struct its parts in place, a scalar one word. *)
Definition inplace_length_def:
  (inplace_length (Bytes NONE) (BytesV bs) = 32 * ((LENGTH bs + 31) DIV 32)) ∧
  (inplace_length String (BytesV bs) = 32 * ((LENGTH bs + 31) DIV 32)) ∧
  (inplace_length (Array _ t) (ListV vs) =
    inplace_lengths (REPLICATE (LENGTH vs) t) vs) ∧
  (inplace_length (Tuple ts) (ListV vs) = inplace_lengths ts vs) ∧
  (inplace_length _ _ = 32) ∧
  (inplace_lengths (t :: ts) (v :: vs) = inplace_length t v + inplace_lengths ts vs) ∧
  (inplace_lengths _ _ = 0)
Termination
  WF_REL_TAC ‘measure (λx. case x of
    INL (t, v) => abi_value_size v
  | INR (ts, vs) => list_size abi_value_size vs)’ >>
  rw[contractABITheory.abi_value_size_def, listTheory.list_size_def]
End

(* How far an in-place encoding's writes reach past its end: each part's
 * spill, less the length of the parts after it. *)
Definition inplace_spill_def:
  (inplace_spill src (Bytes NONE) (BytesV bs) = padded_bytes_spill src (LENGTH bs)) ∧
  (inplace_spill src String (BytesV bs) = padded_bytes_spill src (LENGTH bs)) ∧
  (inplace_spill src (Array _ t) (ListV vs) =
    inplace_parts_spill src (REPLICATE (LENGTH vs) t) vs) ∧
  (inplace_spill src (Tuple ts) (ListV vs) = inplace_parts_spill src ts vs) ∧
  (inplace_spill src _ _ = 0) ∧
  (inplace_parts_spill src (t :: ts) (v :: vs) =
    MAX (inplace_spill src t v - inplace_lengths ts vs)
        (inplace_parts_spill src ts vs)) ∧
  (inplace_parts_spill src _ _ = 0)
Termination
  WF_REL_TAC ‘measure (λx. case x of
    INL (src, t, v) => abi_value_size v
  | INR (src, ts, vs) => list_size abi_value_size vs)’ >>
  rw[contractABITheory.abi_value_size_def, listTheory.list_size_def]
End

(* The in-place encoding an indexed array or struct hashes: its elements or
 * fields concatenated, without lengths or offsets, a nested byte sequence
 * padded. Each part is taken from the part's encoded body (encoded), whose
 * words keep any dirty padding the storage encoder copied. *)
Definition indexed_data_def:
  (indexed_data t a (encoded : byte list) =
    case (t, a) of
      (Array length element, ListV vs) =>
        indexed_parts (REPLICATE (LENGTH vs) element) vs
          (if length = NONE then DROP 32 encoded else encoded) 0
    | (Tuple ts, ListV vs) => indexed_parts ts vs encoded 0
    | (_, BytesV bs) =>
        if is_dynamic t then SOME (TAKE (32 * ((LENGTH bs + 31) DIV 32)) (DROP 32 encoded))
        else SOME (TAKE 32 encoded)
    | _ => SOME (TAKE 32 encoded)) ∧
  (indexed_parts [] [] encoded pos = SOME []) ∧
  (indexed_parts (t :: ts) (v :: vs) encoded pos =
    let dynamic = is_dynamic t in
    let offset = if dynamic then abi_word encoded pos else pos in
    case (indexed_data t v (DROP offset encoded),
          indexed_parts ts vs encoded (pos + if dynamic then 32 else static_length t)) of
      (SOME bs, SOME rest) => SOME (bs ++ rest)
    | _ => NONE) ∧
  (indexed_parts _ _ encoded pos = NONE)
Termination
  WF_REL_TAC ‘measure (λx. case x of
    INL (t, a, encoded) => abi_value_size a
  | INR (ts, vs, encoded, pos) => list_size abi_value_size vs)’ >>
  rw[contractABITheory.abi_value_size_def, listTheory.list_size_def]
End

(* The end of what writes ws cover, from n. *)
Definition writes_end_def:
  (writes_end (n : num) [] = n) ∧
  (writes_end n ((off, bs : byte list) :: ws) = writes_end (MAX n (off + LENGTH bs)) ws)
End

(* The writes, relative to its start, of a partial in the in-place layout
 * (indexed_data): each completed part its in-place bytes and their spill at
 * a running offset, then the failing part's. NONE where the in-place
 * encoding of a whole value is unsupported or ill-formed: a stored part's
 * spill that the later parts' writes don't cover (as inplace_spill counts
 * it for a whole value), or no in-place bytes. *)
Definition inplace_partial_writes_def:
  (inplace_partial_writes src t PartialNone = SOME ([] : (num # byte list) list)) ∧
  (inplace_partial_writes src t (PartialParts len done w q) =
    inplace_parts_writes src 0 (component_types t len (SUC (LENGTH done))) done q) ∧
  (inplace_parts_writes src off [] done q = SOME []) ∧
  (inplace_parts_writes src off (t :: ts) done q =
    case done of
      (a, part_bs, sp) :: rest =>
        (case indexed_data t a part_bs of
           NONE => NONE
         | SOME bs =>
             let n = inplace_spill src t a in
             let next = off + LENGTH bs in
             case inplace_parts_writes src next ts rest q of
               NONE => NONE
             | SOME ws =>
                 if src = StoredBytes ∧ writes_end next ws < next + n then NONE
                 else SOME ((off, bs ++ REPLICATE n 0w) :: ws))
    | [] => OPTION_MAP (shift_writes off) (inplace_partial_writes src t q))
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    INL (src, t, p) => (abi_partial_size p, 0n)
  | INR (src, off, ts, done, q) => (abi_partial_size q, LENGTH ts + 1))’ >>
  rw[]
End

(* The ABI value of v, of type ty, its encoding, the bytes the encoder
 * writes past its end, and how far its reads reach, raised from reach. A
 * storage value is encoded in place (storage_abi_value), its reach its
 * scratch hash's; any other reference is read into its value tree, then
 * encoded. *)
Definition runtime_abi_value_def:
  runtime_abi_value env reach st ty v =
    let ty' = case ty of LocatedT _ t => t | t => t in
    case v of
      ReferenceValue (StorageReference PersistentStorage addr slot 0 rty _) =>
        if rty ≠ ty' then (INR (InvalidCompletion "bad ABI value", PartialNone), reach, st)
        else (case storage_abi_value env (LENGTH env.type_declarations)
                     st.world.accounts addr slot rty of
                (r, w) => (r, scratch_reach reach w, scratch_write w st))
    | _ =>
      case (case v of
              ReferenceValue r => array_copy_value env reach st ty' r
            | _ => (INL v, reach, st)) of
        (INR c, reach1, st1) => (INR c, reach1, st1)
      | (INL tree, reach1, st1) =>
        let t = abi_type env (LENGTH env.type_declarations) ty' in
        case value_abi_value env ty' tree of
          SOME a =>
            (INL (a, enc t a, REPLICATE (abi_spill (encoding_source v) t a) 0w), reach1, st1)
        | NONE => (INR (InvalidCompletion "bad ABI value", PartialNone), reach1, st1)
End

Definition runtime_abi_values_def:
  (runtime_abi_values env reach (st : source_state) [] [] =
     ((INL ([], NONE), reach, st) :
        (((contractABI$abi_type # byte list) list # byte list option) +
         (source_completion # (abi_value # byte list # byte list) list # abi_partial)) #
        num # source_state)) ∧
  (runtime_abi_values env reach st (ty :: tys) (v :: vs) =
    case runtime_abi_value env reach st ty v of
      (INR (c, q), reach1, st1) => (INR (c, [], q), reach1, st1)
    | (INL (a, encoded_body, sp), reach1, st1) =>
      let (r, reach2, st2) = runtime_abi_values env reach1 st1 tys vs in
      ((case r of
          INL (encoded, spill) =>
            let t = abi_type env (LENGTH env.type_declarations) ty in
            INL ((t, encoded_body) :: encoded, later_spill t sp spill)
        | INR (c, done, q) => INR (c, (a, encoded_body, sp) :: done, q)), reach2, st2)) ∧
  (runtime_abi_values _ reach st _ _ =
     (INR (InvalidCompletion "bad ABI arguments", [], PartialNone), reach, st))
End

(* The writes of a tuple of values of types tys, of which the encoder
 * completed done and wrote q of the next. *)
Definition tuple_partial_writes_def:
  tuple_partial_writes env tys done q =
    partial_writes (Tuple (abi_types env (LENGTH env.type_declarations) tys))
      (PartialParts NONE done T q)
End

(* An encoder writes at the free memory pointer, and the compiled one reads
 * each input only when it reaches it, after writing what comes before it.
 * The encoders here read their inputs first, from memory as it was, which
 * gives the same bytes when every input lies below the free pointer. The
 * reads' reach, from zero, is the byte after the last one they touch, a
 * failing read included; an input read at or above the free pointer is
 * unsupported and fails closed before any read failure surfaces. When
 * reading an input ends the frame with a panic or a revert, the encoders
 * give what the compiled one has written by then (abi_partial), as writes
 * relative to where the encoding starts, which the caller makes. *)
Definition encoder_state_def:
  encoder_state (st : source_state) reach (st1 : source_state) =
    if FST (memory_load 64 st) < reach then
      INR (InvalidCompletion "unsupported: encoder input at or above the free memory pointer")
    else INL st1
End

Definition encoded_runtime_values_def:
  encoded_runtime_values env st tys vs =
    let (r, reach, st1) = runtime_abi_values env 0 st tys vs in
    case encoder_state st reach st1 of
      INR c => (INR (c, []), st)
    | INL st2 =>
        case r of
          INL (parts, spill) =>
            (INL (encoded_abi_tuple parts, (case spill of SOME sp => sp | NONE => [])), st2)
        | INR (c, done, q) => (INR (c, tuple_partial_writes env tys done q), st2)
End

(* abi.encodePacked: a value in its own width, a bytesN left-aligned and the
 * others right-aligned in their word; a byte sequence as its contents,
 * wherever it is. Also how far its reads reach, raised from reach: a memory
 * byte sequence's length word and bytes (memory_bytes), a stored one's
 * scratch hash. *)
Definition packed_value_def:
  packed_value env reach st ty v =
    case ty of
      LocatedT _ (ArrayT element length) =>
        if ¬is_stored_scalar_type element then
          (INR (InvalidCompletion "bad packed array", []), reach, st)
        else
          (case runtime_abi_value env reach st ty v of
             (INL (_, bs, _), reach1, st1) =>
               (INL (case length of NONE => DROP 32 bs | SOME _ => bs), reach1, st1)
           | (INR (c, q), reach1, st1) =>
               (case inplace_partial_writes (encoding_source v)
                       (abi_type env (LENGTH env.type_declarations) ty) q of
                  SOME ws => (INR (c, ws), reach1, st1)
                | NONE => (INR (InvalidCompletion "bad packed array", []), reach1, st1)))
    | LocatedT _ _ =>
        (case v of
           ReferenceValue r =>
             (case byte_contents st r of
                INL (bs, st1) =>
                  (INL bs,
                   (case r of
                      MemoryReference p _ =>
                        touched_reach (touched_reach reach p 32) (p + 32) (LENGTH bs)
                    | StorageReference _ addr slot _ _ _ =>
                        scratch_reach reach (long_bytes_scratch st.world.accounts addr slot)
                    | _ => reach),
                   st1)
              | INR c => (INR (c, []), reach, st))
         | ScalarValue (BytesValue bs) => (INL bs, reach, st)
         | _ => (INR (InvalidCompletion "bad packed value", []), reach, st))
    | _ =>
      case (abi_value ty v, storage_bytes ty) of
        (SOME a, SOME width) =>
          let word = enc (abi_type env 0 ty) a in
          (INL (case ty of
                  FixedBytesT _ => TAKE width word
                | _ => DROP (32 - width) word), reach, st)
      | _ => (INR (InvalidCompletion "bad packed value", []), reach, st)
End

(* The parts written one after another, and the bytes left past their end:
 * the later parts' own, then what of a part's tail reaches past those. *)
Definition packed_values_def:
  (packed_values env reach st [] [] =
     ((INL ([], []), reach, st) :
        ((byte list # byte list) + (source_completion # (num # byte list) list)) #
        num # source_state)) ∧
  (packed_values env reach st (ty :: tys) (v :: vs) =
    case packed_value env reach st ty v of
      (INR c, reach1, st1) => (INR c, reach1, st1)
    | (INL bs, reach1, st1) =>
      let (r, reach2, st2) = packed_values env reach1 st1 tys vs in
      let tail = packed_tail st1.world.accounts ty v bs in
      ((case r of
          INL (rest, spill) =>
            INL (bs ++ rest, spill ++ DROP (LENGTH rest + LENGTH spill) tail)
        | INR (c, ws) => INR (c, (0, bs ++ tail) :: shift_writes (LENGTH bs) ws)),
       reach2, st2)) ∧
  (packed_values _ reach st _ _ =
     (INR (InvalidCompletion "bad packed values", []), reach, st))
End

Definition packed_encoding_def:
  packed_encoding env st tys vs =
    let (r, reach, st1) = packed_values env 0 st tys vs in
    case encoder_state st reach st1 of
      INR c => (INR (c, []), st)
    | INL st2 => (r, st2)
End

Definition abi_runtime_values_def:
  (abi_runtime_values [] [] = SOME []) ∧
  (abi_runtime_values (ty :: tys) (a :: as) =
    case (abi_runtime_value ty a, abi_runtime_values tys as) of
      (SOME v, SOME vs) => SOME (v :: vs)
    | _ => NONE) ∧
  (abi_runtime_values _ _ = NONE)
End

(* A memory value decoded at pos, as the pinned decoder does: a scalar
 * validated in place (an enum outside its members reverts); a byte sequence
 * or array whose encoding starts at pos in range, its length below 2^64 and
 * its memory allocated (Panic(0x41) when the free memory pointer would pass
 * 2^64) before its data span is checked; a struct whose heads lie within the
 * data, allocated after that check; then each element or field, a dynamic
 * one at an offset below 2^64 from the start of the array's data or of the
 * struct. Offsets need not be aligned, tails may overlap, and padding is
 * ignored. Byte sequences decode to their bytes, and arrays and structs to
 * the tuple of their elements or fields; free is the free memory pointer,
 * and reach the end of the input the decoder has read, as its mloads and
 * mcopys reach. A byte sequence or array whose data reaches past bound is
 * left unsupported: a memory input's bound is where the free memory pointer
 * was, past which the compiled decoder's own allocations may lie. The
 * compiled decoder reads the free memory pointer anew for each object it
 * allocates, where free here only advances: an allocation below 96, whose
 * object can cover the pointer's word, is left unsupported. The fuel bounds
 * the struct nesting. *)
Definition decode_memory_value_def:
  (decode_memory_value env (fuel : num) ty bs (total : num) (bound : num) pos free (reach : num) =
    if byte_sequence_type ty ∨ (case ty of ArrayT _ _ => T | _ => F) then
      if pos + 32 > total then INR (RevertCompletion []) else
      let (length, data, size, reach1) =
        case ty of
          ArrayT element (SOME n) => (n, pos, 32 * n, reach)
        | ArrayT element NONE =>
            let n = input_word bs pos in (n, pos + 32, 32 + 32 * n, MAX reach (pos + 32))
        | _ => let n = input_word bs pos in
               (n, pos + 32, 32 + 32 * ((n + 31) DIV 32), MAX reach (pos + 32)) in
      if 2 ** 64 ≤ length ∨ 2 ** 64 ≤ free + size then INR (PanicCompletion 65) else
      if free < 96 then INR (InvalidCompletion "unsupported: decoding into memory below the free memory pointer word's end") else
      case ty of
        ArrayT element _ =>
          if data + length * abi_stride env element > total then
            INR (RevertCompletion [])
          else if data + length * abi_stride env element > bound then
            INR (InvalidCompletion "unsupported: abi.decode reading at the free memory pointer")
          else
            (case decode_memory_elements env fuel element bs total bound data 0 length (free + size)
                    reach1 of
               INL (vs, next, reach2) => INL (TupleValue vs, next, reach2)
             | INR c => INR c)
      | _ =>
          if data + length > total then INR (RevertCompletion [])
          else if data + length > bound then
            INR (InvalidCompletion "unsupported: abi.decode reading at the free memory pointer")
          else INL (ScalarValue (BytesValue (input_bytes bs data length)), free + size,
                    MAX reach1 (data + length))
    else case ty of
      StructT s =>
        (case lookup_struct env s of
           SOME fields =>
             let tys = MAP SND fields in
             if pos + head_lengths (abi_types env (LENGTH env.type_declarations) tys) 0 >
                total
             then INR (RevertCompletion [])
             else if 2 ** 64 ≤ free + 32 * LENGTH tys then INR (PanicCompletion 65)
             else if free < 96 then INR (InvalidCompletion "unsupported: decoding into memory below the free memory pointer word's end")
             else if fuel = 0 then INR (InvalidCompletion "struct nesting")
             else
               (case decode_memory_fields env (fuel - 1) tys bs total bound pos pos
                       (free + 32 * LENGTH tys) reach of
                  INL (vs, next, reach1) => INL (TupleValue vs, next, reach1)
                | INR c => INR c)
         | NONE => INR (InvalidCompletion "unknown struct"))
    | _ =>
      let a = abi_type env 0 ty in
      let word = input_bytes bs pos 32 in
      if pos + 32 > total ∨ ¬valid_enc a word then
        INR (RevertCompletion [])
      else
        case abi_runtime_value ty (dec a word) of
          SOME (ScalarValue v) =>
            if (case ty of EnumT _ => ¬scalar_has_type env ty v | _ => F) then
              INR (RevertCompletion [])
            else INL (ScalarValue v, free, MAX reach (pos + 32))
        | _ => INR (InvalidCompletion "bad ABI scalar type")) ∧
  (decode_memory_elements env fuel element bs total bound data i n free reach =
    if n = 0 then INL ([], free, reach) else
    case decode_memory_part env fuel element bs total bound data
           (data + i * abi_stride env element) free reach of
      INR c => INR c
    | INL (v, next, reach1) =>
        case decode_memory_elements env fuel element bs total bound data (i + 1) (n - 1) next
               reach1 of
          INL (vs, last, reach2) => INL (v :: vs, last, reach2)
        | INR c => INR c) ∧
  (decode_memory_fields env fuel [] bs total bound base src free reach = INL ([], free, reach)) ∧
  (decode_memory_fields env fuel (ty :: tys) bs total bound base src free reach =
    case decode_memory_part env fuel ty bs total bound base src free reach of
      INR c => INR c
    | INL (v, next, reach1) =>
        case decode_memory_fields env fuel tys bs total bound base (src + abi_stride env ty) next
               reach1 of
          INL (vs, last, reach2) => INL (v :: vs, last, reach2)
        | INR c => INR c) ∧
  (* An element or field whose head is at src: a dynamic one at the offset
   * there from base. *)
  (decode_memory_part env fuel ty bs total bound base src free reach =
    if is_dynamic (abi_type env (LENGTH env.type_declarations) ty) then
      let offset = input_word bs src in
      if 2 ** 64 ≤ offset then INR (RevertCompletion [])
      else decode_memory_value env fuel ty bs total bound (base + offset) free
             (MAX reach (src + 32))
    else decode_memory_value env fuel ty bs total bound src free reach)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (_, fuel, ty, _) => (fuel, sol_type_size ty, 1)
  | INR (INL (_, fuel, element, _, _, _, _, _, n, _)) =>
      (fuel, sol_type_size element, n + 3)
  | INR (INR (INL (_, fuel, tys, _))) =>
      (fuel, list_size sol_type_size tys, 0)
  | INR (INR (INR (_, fuel, ty, _))) =>
      (fuel, sol_type_size ty, 2))’ >>
  rw[solidityASTTheory.sol_type_size_def, listTheory.list_size_def]
End

(* A calldata object copied to memory: check allocation before its data span,
 * then read its value for materialization. Byte copies use word addition
 * for the span and calldatacopy's zero filling; an array is decoded as an ABI
 * argument after its span check, and a struct as an ABI argument is. *)
Definition copy_calldata_array_def:
  copy_calldata_array env cd ty data length free =
    if byte_sequence_type ty then
      let size = 32 + 32 * ((length + 31) DIV 32) in
      if 2 ** 64 ≤ length ∨ 2 ** 64 ≤ free + size then INR (PanicCompletion 65)
      else if LENGTH cd < (data + length) MOD 2 ** 256 then INR (RevertCompletion [])
      else INL (ScalarValue (BytesValue
             (TAKE length (DROP data cd ++ REPLICATE length 0w))))
    else case ty of
      ArrayT element l =>
        let size = (if l = NONE then 32 else 0) + 32 * length in
        if 2 ** 64 ≤ free + size then INR (PanicCompletion 65)
        else if free < 96 then INR (InvalidCompletion "unsupported: decoding into memory below the free memory pointer word's end")
        else if data + length * abi_stride env element > LENGTH cd then
          INR (RevertCompletion [])
        else (case decode_memory_elements env (LENGTH env.type_declarations) element cd
                     (LENGTH cd) (LENGTH cd) data 0 length (free + size) 0 of
                INL (vs, _) => INL (TupleValue vs)
              | INR c => INR c)
    | StructT _ =>
        (case decode_memory_value env (LENGTH env.type_declarations) ty cd (LENGTH cd) (LENGTH cd) data free 0 of
           INL (v, _) => INL v
         | INR c => INR c)
    | _ => INR (InvalidCompletion "bad calldata copy")
End

(* An argument at head: a scalar, static array or static struct in place, any
 * other value at the offset the head holds, below 2^64. A calldata argument
 * stays in the calldata: a byte sequence or dynamic array with its data in
 * range, any other dynamic value with its heads in range. *)
Definition decode_abi_argument_def:
  decode_abi_argument env ty bs (total : num) (bound : num) head base free reach =
    if head + 32 > total then INR (RevertCompletion []) else
    case ty of
      LocatedT CalldataLoc element =>
        let a = abi_type env (LENGTH env.type_declarations) element in
        if ¬is_dynamic a then
          INL (ReferenceValue (CalldataReference (base + head) (calldata_length element)
                 element), free, reach)
        else
        let offset = input_word bs head in
        if byte_sequence_type element ∨ (case element of ArrayT _ NONE => T | _ => F) then
          if 2 ** 64 ≤ offset ∨ offset + 32 > total then
            INR (RevertCompletion []) else
          let length = input_word bs offset in
          let stride = case element of ArrayT inner NONE => abi_stride env inner | _ => 1 in
          if 2 ** 64 ≤ length ∨ offset + 32 + length * stride > total then
            INR (RevertCompletion [])
          else INL (ReferenceValue (CalldataReference (base + offset + 32) length element),
                    free, MAX reach (MAX (head + 32) (offset + 32)))
        else if 2 ** 64 ≤ offset ∨ offset + abi_head_size a > total then
          INR (RevertCompletion [])
        else INL (ReferenceValue (CalldataReference (base + offset)
                    (calldata_length element) element), free, MAX reach (head + 32))
    | LocatedT MemoryLoc element =>
        decode_memory_part env (LENGTH env.type_declarations) element bs total bound 0 head free
          reach
    | _ => decode_memory_value env (LENGTH env.type_declarations) ty bs total bound head free reach
End

Definition decode_abi_arguments_def:
  (decode_abi_arguments env [] bs total bound head base free reach = INL ([], reach)) ∧
  (decode_abi_arguments env (ty :: tys) bs total bound head base free reach =
    case decode_abi_argument env ty bs total bound head base free reach of
      INR c => INR c
    | INL (v, next, reach1) =>
        case decode_abi_arguments env tys bs total bound (head + abi_stride env ty) base next
               reach1 of
          INL (vs, reach2) => INL (v :: vs, reach2)
        | INR c => INR c)
End

(* Arguments decoded from an input of total bytes, of which bs holds the
 * leading ones; the rest read as zeros. Memory is decoded in place this way,
 * as the compiler's decoder reads only the words it needs; with the
 * arguments comes the end of the input it read. Data reaching past bound is
 * left unsupported (decode_memory_value). *)
Definition decode_input_def:
  decode_input env tys bs total bound base free =
    if head_lengths (abi_types env (LENGTH env.type_declarations) tys) 0 > total then
      INR (RevertCompletion [])
    else decode_abi_arguments env tys bs total bound 0 base free 0
End

Definition decode_arguments_def:
  decode_arguments env tys bs base free =
    case decode_input env tys bs (LENGTH bs) (LENGTH bs) base free of
      INL (vs, _) => INL vs
    | INR c => INR c
End

(* A decoded value written to memory as the compiler's abi_decode functions write
 * it, allocating in decoding order: an array or struct, its length word if
 * dynamic, then each element or field, a reference one allocated before its
 * pointer is stored; a byte sequence copied with cleanup. *)
Definition materialize_value_def:
  (materialize_value env ty v (st : source_state) =
    case (ty, v) of
      (ArrayT element length, TupleValue vs) =>
        let n = LENGTH vs in
        (case allocate_memory ((if length = NONE then 32 else 0) + 32 * n) st of
           INR c => INR c
         | INL (p, st1) =>
             let st2 = if length = NONE then memory_store p n st1 else st1 in
             (case materialize_words env (REPLICATE n element) vs
                     (if length = NONE then p + 32 else p) st2 of
                INL st3 => INL (ReferenceValue (MemoryReference p ty), st3)
              | INR c => INR c))
    | (StructT s, TupleValue vs) =>
        (case lookup_struct env s of
           SOME fields =>
             (case allocate_memory (32 * LENGTH vs) st of
                INR c => INR c
              | INL (p, st1) =>
                  (case materialize_words env (MAP SND fields) vs p st1 of
                     INL st2 => INL (ReferenceValue (MemoryReference p ty), st2)
                   | INR c => INR c))
         | NONE => INR (InvalidCompletion "unknown struct"))
    | (_, ScalarValue (BytesValue bs)) =>
        if byte_sequence_type ty then
          (case new_byte_array bs st of
             INL (p, st1) => INL (ReferenceValue (MemoryReference p ty), st1)
           | INR c => INR c)
        else INL (v, st)
    | (_, ScalarValue _) => INL (v, st)
    | _ => INR (InvalidCompletion "bad decoded value")) ∧
  (materialize_words env [] [] p st = INL st) ∧
  (materialize_words env (ty :: tys) (v :: vs) p st =
    case materialize_value env ty v st of
      INR c => INR c
    | INL (value, st1) =>
        case write_memory_word env ty p value st1 of
          INR c => INR c
        | INL st2 => materialize_words env tys vs (p + 32) st2) ∧
  (materialize_words env _ _ p st = INR (InvalidCompletion "bad decoded value"))
Termination
  WF_REL_TAC ‘measure (λx. case x of
    INL (env, ty, v, st) => runtime_value_size v
  | INR (env, tys, vs, p, st) => list_size runtime_value_size vs)’ >>
  rw[solidityCoreTheory.runtime_value_size_def, listTheory.list_size_def]
End

(* A storage array, struct or byte sequence copied to new memory, as the
 * compiler's storage-to-memory copies do. A byte sequence or an array of
 * scalars is written at the free memory pointer first and its allocation
 * finalized after, as the compiled copy encodes at allocate_unbounded() and
 * then calls finalize_allocation; an array of references or a struct is
 * allocated before its members. A dynamic array, and a long byte sequence,
 * hashes its slot in scratch word 0 (array_dataslot) right after its length
 * is written, before its data. Scalars are read cleaned, and a byte
 * sequence keeps whole data words (storage_byte_data); an empty one still
 * writes its slot's word after its length, past the allocation. A length of
 * 2^64 or more panics with 0x41 where the copy allocates first; where it
 * encodes first it is unsupported, as the compiled encoder has no length
 * check (it runs out of gas, or panics cleaning an element). A failure keeps
 * the state it reached, with the memory written before it. The fuel bounds
 * the struct nesting. *)
Definition materialize_storage_def:
  (materialize_storage env (fuel : num) accounts addr slot ty st =
    if byte_sequence_type ty then
      (case storage_byte_length accounts addr slot of
         INR c => INR (c, st)
       | INL length =>
           if 2 ** 64 ≤ length then
             INR (InvalidCompletion
                    "unsupported: a stored sequence of 2^64 or more elements encoded to memory",
                  st) else
           let (p, st1) = memory_load 64 st;
               st2 = memory_write (p + 32)
                       (storage_byte_data accounts addr slot length)
                       (scratch_write (long_bytes_scratch accounts addr slot)
                          (memory_store p length st1)) in
           case finalize_allocation p ((length + 31) DIV 32 * 32 + 32) st2 of
             INR c => INR (c, st2)
           | INL st3 => INL (ReferenceValue (MemoryReference p ty), st3))
    else case ty of
      ArrayT element l =>
        (case storage_array_data accounts addr slot ty of
           (length, data) =>
             let size = (if l = NONE then 32 else 0) + 32 * length;
                 scalars = is_stored_scalar_type element in
             if 2 ** 64 ≤ length then
               INR (if scalars then
                      InvalidCompletion
                        "unsupported: a stored sequence of 2^64 or more elements encoded to memory"
                    else PanicCompletion 65, st) else
             case (if scalars then INL (memory_load 64 st)
                   else allocate_memory size st) of
               INR c => INR (c, st)
             | INL (p, st1) =>
                 let st2 = if l = NONE then
                             scratch_write (SOME slot) (memory_store p length st1)
                           else st1 in
                 case materialize_storage_elements env fuel accounts addr data element
                        0 length (if l = NONE then p + 32 else p) st2 of
                   INL st3 =>
                     (case (if scalars then finalize_allocation p size st3
                            else INL st3) of
                        INL st4 => INL (ReferenceValue (MemoryReference p ty), st4)
                      | INR c => INR (c, st3))
                 | INR r => INR r)
    | StructT s =>
        (case (lookup_struct env s, lookup_struct_layout env s) of
           (SOME fields, SOME layout) =>
             if fuel = 0 then INR (InvalidCompletion "struct nesting", st) else
             (case allocate_memory (32 * LENGTH fields) st of
                INR c => INR (c, st)
              | INL (p, st1) =>
                  case materialize_storage_fields env (fuel - 1) accounts addr slot
                         layout.struct_fields fields p st1 of
                    INL st2 => INL (ReferenceValue (MemoryReference p ty), st2)
                  | INR r => INR r)
         | _ => INR (InvalidCompletion "missing struct layout", st))
    | _ => INR (InvalidCompletion "bad storage array type", st)) ∧
  (materialize_storage_elements env fuel accounts addr data element i n q st =
    if n = 0 then INL st else
    case storage_element_location env data element i of
      NONE => INR (InvalidCompletion "bad array element type", st)
    | SOME (s, offset) =>
        let value =
          if is_stored_scalar_type element then
            (case read_storage env accounts addr s offset element of
               SOME v => INL (ScalarValue v, st)
             | NONE => INR (InvalidCompletion "bad storage read", st))
          else materialize_storage env fuel accounts addr s element st in
        case value of
          INR r => INR r
        | INL (v, st1) =>
            case write_memory_word env element q v st1 of
              INR c => INR (c, st1)
            | INL st2 =>
                materialize_storage_elements env fuel accounts addr data element
                  (i + 1) (n - 1) (q + 32) st2) ∧
  (materialize_storage_fields env fuel accounts addr slot layout [] q st = INL st) ∧
  (materialize_storage_fields env fuel accounts addr slot layout ((f, ty) :: fields) q st =
    case ALOOKUP (MAP (λv. (v.state_id, v)) layout) f of
      NONE => INR (InvalidCompletion "missing field layout", st)
    | SOME v =>
        let s = slot + v.state_slot in
        let value =
          if is_stored_scalar_type ty then
            (case read_storage env accounts addr s v.state_offset ty of
               SOME x => INL (ScalarValue x, st)
             | NONE => INR (InvalidCompletion "bad storage read", st))
          else materialize_storage env fuel accounts addr s ty st in
        case value of
          INR r => INR r
        | INL (x, st1) =>
            case write_memory_word env ty q x st1 of
              INR c => INR (c, st1)
            | INL st2 =>
                materialize_storage_fields env fuel accounts addr slot layout fields
                  (q + 32) st2)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (env, fuel, accounts, addr, slot, ty, st) => (fuel, sol_type_size ty, 0)
  | INR (INL (env, fuel, accounts, addr, data, element, i, n, q, st)) =>
      (fuel, sol_type_size element, n + 1)
  | INR (INR (env, fuel, accounts, addr, slot, layout, fields, q, st)) =>
      (fuel, list_size (sol_type_size o SND) fields, 1))’ >>
  rw[solidityASTTheory.sol_type_size_def, listTheory.list_size_def]
End

(* Decoded memory payloads are written to memory before a procedure sees them.
 * Calldata payloads retain slices into the frame's original call_data. *)
Definition materialize_arguments_def:
  (materialize_arguments env [] [] st = INL ([], st)) ∧
  (materialize_arguments env (ty :: tys) (v :: vs) st =
    case (case ty of
            LocatedT MemoryLoc element => materialize_value env element v st
          | _ => INL (v, st)) of
      INL (value, st1) =>
        (case materialize_arguments env tys vs st1 of
           INL (values, st2) => INL (value :: values, st2)
         | INR c => INR c)
    | INR c => INR c) ∧
  (materialize_arguments _ _ _ _ = INR (InvalidCompletion "bad decoded arguments"))
End

(* Revert data of Panic(uint256), selector 0x4e487b71. *)
Definition panic_data_def:
  panic_data n = [0x4Ew; 0x48w; 0x7Bw; 0x71w] ++ enc (Uint 256) (NumV n)
End

(* Temporaries written one after another, each at the free memory pointer
 * as memory holds it when the temporary is written: the compiler reads the
 * pointer anew for each, which an earlier temporary may have overwritten.
 * Also gives the least pointer read, counting the one read after the last
 * temporary. *)
Definition write_at_each_def:
  (write_at_each [] st = (FST (memory_load 64 st), st)) ∧
  (write_at_each (bs :: rest) st =
     let (p, st1) = memory_load 64 st in
     let st2 = memory_write p bs st1 in
     let (least, st3) = write_at_each rest st2 in
     (MIN p least, st3))
End

(* An indexed event argument: an array or struct hashes its in-place
 * encoding, a byte sequence its bytes, a scalar its ABI word. Gives the
 * topic and the bytes hashed for it at the free memory pointer; on a failed
 * read, what the compiled emit has written there of its in-place encoding. *)
Definition event_part_def:
  event_part env reach st ty v =
    let t = abi_type env (LENGTH env.type_declarations) ty in
    let composite = (case t of Array _ _ => T | Tuple _ => T | _ => F) in
    let src = encoding_source v in
    case runtime_abi_value env reach st ty v of
      (INR (c, q), reach1, st1) =>
        (case (if composite then inplace_partial_writes src t q else SOME []) of
           SOME ws => (INR (c, ws), reach1, st1)
         | NONE =>
             (INR (InvalidCompletion
                     "unsupported: a partial in-place encoding of an indexed array or struct",
                   []), reach1, st1))
    | (INL (a, encoded_body, sp), reach1, st1) =>
        if composite ∧ src = StoredBytes ∧ inplace_spill src t a ≠ 0 then
          (INR (InvalidCompletion
                  "unsupported: an indexed stored array or struct ending in empty bytes", []),
           reach1, st1)
        else
        let topic =
          if composite then
            OPTION_MAP (λbs. (word_of_bytes_be (Keccak_256_w64 bs),
                              [bs ++ REPLICATE (inplace_spill src t a) 0w]))
              (indexed_data t a encoded_body)
          else case a of
            BytesV bs =>
              SOME (if is_dynamic t then
                      (word_of_bytes_be (Keccak_256_w64 bs),
                       [bs ++ packed_bytes_tail st1.world.accounts v bs])
                    else (word_of_bytes T (0w : bytes32) encoded_body, []))
          | _ => SOME (word_of_bytes T (0w : bytes32) encoded_body, []) in
        (case topic of
           SOME (word, temp) => (INL (word, temp), reach1, st1)
         | NONE => (INR (InvalidCompletion "bad indexed event argument", []), reach1, st1))
End

(* The indexed arguments' topics, every hash preimage produced before a
 * failing read, and the reach and state reached up to and including that
 * read. *)
Definition event_parts_def:
  (event_parts env reach st [] = (INL [], [], reach, st)) ∧
  (event_parts env reach st ((ty, v) :: args) =
    case event_part env reach st ty v of
      (INR c, reach1, st1) => (INR c, [], reach1, st1)
    | (INL (word, temp), reach1, st1) =>
        let (r, temps, reach2, st2) = event_parts env reach1 st1 args in
        ((case r of INL topics => INL (word :: topics) | INR c => INR c),
         temp ++ temps, reach2, st2))
End

(* The post-read fail-closed checks for emit: the encoder's free-pointer reach
 * check, then writing the indexed hash preimages at the free memory pointer.
 * The compiled emit reads the pointer anew for each preimage and for the
 * log's data, so a preimage that moves the pointer below the reads' reach
 * fails closed before any read failure surfaces: a later preimage or the
 * data could overwrite an input, or a scratch hash the data. *)
Definition event_state_def:
  event_state st temps reach st1 =
    case encoder_state st reach st1 of
      INR c => INR c
    | INL st2 =>
        let (least, st3) = write_at_each temps st2 in
        if least < reach then
          INR (InvalidCompletion
            "unsupported: encoder reach overlaps a free memory pointer moved by an event's hash preimage")
        else INL st3
End

(* The compiled emit reads the indexed arguments for their topics before it
 * encodes the others as the log's data. On a failed read, the writes are
 * relative to the free memory pointer after the hash preimages. *)
Definition event_log_def:
  event_log env st logger topic0 args =
    let (r, temps, reach, st1) =
      event_parts env 0 st
        (MAP (λ(ty, indexed, v). (ty, v)) (FILTER (λ(ty, indexed, v). indexed) args)) in
    let data_args = FILTER (λ(ty, indexed, v). ¬indexed) args in
    let tys = MAP FST data_args in
    case r of
      INR (c, ws) =>
        (case event_state st temps reach st1 of
           INR c1 => (INR (c1, []), st)
         | INL st2 => (INR (c, ws), st2))
    | INL topics =>
        let (r2, reach2, st2) =
          runtime_abi_values env reach st1 tys (MAP (SND o SND) data_args) in
        case event_state st temps reach2 st2 of
          INR c => (INR (c, []), st)
        | INL st3 =>
            case r2 of
              INL (parts, spill) =>
                (INL (<| logger := logger;
                         topics := (case topic0 of SOME t => t :: topics | NONE => topics);
                         data := encoded_abi_tuple parts |>,
                      (case spill of SOME sp => sp | NONE => [])), st3)
            | INR (c, done, q) => (INR (c, tuple_partial_writes env tys done q), st3)
End

val abi_type_pre_def = cv_auto_trans_pre_rec "abi_type_pre abi_types_pre" abi_type_def (
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    INL (env, fuel, ty) => (cv$c2n fuel, cv_size ty)
  | INR (env, fuel, tys) => (cv$c2n fuel, cv_size tys))’ >>
  cv_termination_tac
);

Theorem abi_type_pre[cv_pre]:
  (∀env fuel ty. abi_type_pre env fuel ty) ∧
  (∀env fuel tys. abi_types_pre env fuel tys)
Proof
  ho_match_mp_tac abi_type_ind >> rpt strip_tac >>
  simp[Once abi_type_pre_def] >> rw[] >> gvs[]
QED
val () = cv_auto_trans abi_value_def;
val value_abi_value_pre_def = cv_auto_trans_pre_rec
  "value_abi_value_pre values_abi_value_pre fields_abi_value_pre" value_abi_value_def (
  WF_REL_TAC ‘measure (λx. case x of
    INL (env, ty, v) => cv_size v
  | INR (INL (env, element, vs)) => cv_size vs
  | INR (INR (env, tys, vs)) => cv_size vs)’ >>
  cv_termination_tac
);

Theorem value_abi_value_pre[cv_pre]:
  (∀env ty v. value_abi_value_pre env ty v) ∧
  (∀env element vs. values_abi_value_pre env element vs) ∧
  (∀env tys vs. fields_abi_value_pre env tys vs)
Proof
  ho_match_mp_tac value_abi_value_ind >> rpt strip_tac >>
  simp[Once value_abi_value_pre_def] >> rw[] >> gvs[]
QED
val () = cv_auto_trans encoding_source_def;
val () = cv_auto_trans padded_bytes_spill_def;
val () = cv_auto_trans later_spill_def;
val abi_spill_pre_def = cv_auto_trans_pre_rec "abi_spill_pre parts_spill_pre" abi_spill_def (
  WF_REL_TAC ‘measure (λx. case x of
    INL (src, t, v) => cv_size v
  | INR (src, ts, vs) => cv_size vs)’ >>
  cv_termination_tac
);

Theorem abi_spill_pre[cv_pre]:
  (∀src t v. abi_spill_pre src t v) ∧ (∀src ts vs. parts_spill_pre src ts vs)
Proof
  ho_match_mp_tac abi_spill_ind >> rpt strip_tac >>
  simp[Once abi_spill_pre_def] >> rw[] >> gvs[]
QED
val () = cv_auto_trans tree_part_def;
val () = cv_auto_trans shift_writes_def;
val () = cv_auto_trans component_types_def;
val () = cv_auto_trans parts_head_length_def;
val partial_writes_pre_def = cv_auto_trans_pre_rec
  "partial_writes_pre parts_writes_pre" partial_writes_def (
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    INL (t, p) => (cv_size p, 0n)
  | INR (hl, h, tl, ts, done, w, q) => (cv_size q, cv_size ts + 1))’ >>
  cv_termination_tac
);

Theorem partial_writes_pre[cv_pre]:
  (∀t p. partial_writes_pre t p) ∧
  (∀hl h tl ts done w q. parts_writes_pre hl h tl ts done w q)
Proof
  ho_match_mp_tac partial_writes_ind >> rpt strip_tac >>
  simp[Once partial_writes_pre_def] >> rw[] >> gvs[]
QED

val () = cv_auto_trans apply_writes_def;
val memory_value_pre_def = cv_auto_trans_pre_rec
  "memory_value_pre memory_elements_pre memory_fields_pre" memory_value_def (
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (env, fuel, ty, v, reach, st) => (cv$c2n fuel, cv_size ty, 0)
  | INR (INL (env, fuel, element, p, n, reach, st)) =>
      (cv$c2n fuel, cv_size element, cv$c2n n + 1)
  | INR (INR (env, fuel, tys, p, reach, st)) => (cv$c2n fuel, cv_size tys, 1))’ >>
  cv_termination_tac
);

Theorem memory_value_pre[cv_pre]:
  (∀env fuel ty v reach st. memory_value_pre env fuel ty v reach st) ∧
  (∀env fuel element p n reach st.
     memory_elements_pre env fuel element p n reach st) ∧
  (∀env fuel tys p reach st. memory_fields_pre env fuel tys p reach st)
Proof
  ho_match_mp_tac memory_value_ind >> rpt strip_tac >>
  simp[Once memory_value_pre_def] >> rw[] >> gvs[]
QED

val () = cv_auto_trans abi_runtime_value_def;
val () = cv_auto_trans abi_runtime_values_def;
val () = cv_auto_trans abi_word_def;
val () = cv_auto_trans input_bytes_def;
val () = cv_auto_trans input_word_def;
val () = cv_auto_trans abi_stride_def;
val () = cv_auto_trans abi_head_size_def;
val () = cv_auto_trans calldata_length_def;
val () = cv_auto_trans calldata_word_def;
val () = cv_auto_trans calldata_offset_def;
val () = cv_auto_trans calldata_tail_def;
val () = cv_auto_trans calldata_part_def;
val () = cv_auto_trans calldata_struct_field_def;
val calldata_value_pre_def = cv_auto_trans_pre_rec
  "calldata_value_pre calldata_values_pre calldata_fields_pre calldata_part_value_pre"
  calldata_value_def (
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (_, fuel, _, ty, _, _) => (cv$c2n fuel, cv_size ty, 0)
  | INR (INL (_, fuel, _, element, _, _, n)) =>
      (cv$c2n fuel, cv_size element, cv$c2n n + 2)
  | INR (INR (INL (_, fuel, _, tys, _, _))) => (cv$c2n fuel, cv_size tys, 0)
  | INR (INR (INR (_, fuel, _, ty, _, _))) => (cv$c2n fuel, cv_size ty, 1))’ >>
  cv_termination_tac
);

Theorem calldata_value_pre[cv_pre]:
  (∀env fuel cd ty data length. calldata_value_pre env fuel cd ty data length) ∧
  (∀env fuel cd element data i n. calldata_values_pre env fuel cd element data i n) ∧
  (∀env fuel cd tys base head. calldata_fields_pre env fuel cd tys base head) ∧
  (∀env fuel cd ty base head. calldata_part_value_pre env fuel cd ty base head)
Proof
  ho_match_mp_tac calldata_value_ind >> rpt strip_tac >>
  simp[Once calldata_value_pre_def] >> rw[] >> gvs[]
QED
val () = cv_auto_trans encoded_abi_parts_def;
val () = cv_auto_trans encoded_abi_tuple_def;
val last_spill_pre_def = cv_auto_trans_pre "last_spill_pre" last_spill_def;

Theorem last_spill_pre[cv_pre,local]:
  ∀ps. last_spill_pre ps
Proof
  Induct >> rw[Once last_spill_pre_def]
QED

val storage_abi_value_pre_def = cv_auto_trans_pre_rec
  "storage_abi_value_pre storage_abi_elements_pre storage_abi_fields_pre"
  storage_abi_value_def (
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (env, fuel, accounts, addr, slot, ty) => (cv$c2n fuel, cv_size ty, 0)
  | INR (INL (env, fuel, accounts, addr, data, element, i, n)) =>
      (cv$c2n fuel, cv_size element, cv$c2n n + 1)
  | INR (INR (env, fuel, accounts, addr, slot, layout, fields)) =>
      (cv$c2n fuel, cv_size fields, 1))’ >>
  cv_termination_tac
);

Theorem storage_abi_value_pre[cv_pre]:
  (∀env fuel accounts addr slot ty. storage_abi_value_pre env fuel accounts addr slot ty) ∧
  (∀env fuel accounts addr data element i n.
     storage_abi_elements_pre env fuel accounts addr data element i n) ∧
  (∀env fuel accounts addr slot layout fields.
     storage_abi_fields_pre env fuel accounts addr slot layout fields)
Proof
  ho_match_mp_tac storage_abi_value_ind >> rpt strip_tac >>
  simp[Once storage_abi_value_pre_def] >> rw[] >> gvs[]
QED
val () = cv_auto_trans array_copy_value_def;

val () = cv_auto_trans packed_bytes_tail_def;
val () = cv_auto_trans packed_tail_def;
val inplace_length_pre_def = cv_auto_trans_pre_rec
  "inplace_length_pre inplace_lengths_pre" inplace_length_def (
  WF_REL_TAC ‘measure (λx. case x of
    INL (t, v) => cv_size v
  | INR (ts, vs) => cv_size vs)’ >>
  cv_termination_tac
);

Theorem inplace_length_pre[cv_pre]:
  (∀t v. inplace_length_pre t v) ∧ (∀ts vs. inplace_lengths_pre ts vs)
Proof
  ho_match_mp_tac inplace_length_ind >> rpt strip_tac >>
  simp[Once inplace_length_pre_def] >> rw[] >> gvs[]
QED

val inplace_spill_pre_def = cv_auto_trans_pre_rec
  "inplace_spill_pre inplace_parts_spill_pre" inplace_spill_def (
  WF_REL_TAC ‘measure (λx. case x of
    INL (src, t, v) => cv_size v
  | INR (src, ts, vs) => cv_size vs)’ >>
  cv_termination_tac
);

Theorem inplace_spill_pre[cv_pre]:
  (∀src t v. inplace_spill_pre src t v) ∧ (∀src ts vs. inplace_parts_spill_pre src ts vs)
Proof
  ho_match_mp_tac inplace_spill_ind >> rpt strip_tac >>
  simp[Once inplace_spill_pre_def] >> rw[] >> gvs[]
QED
val indexed_data_pre_def = cv_auto_trans_pre_rec
  "indexed_data_pre indexed_parts_pre" indexed_data_def (
  WF_REL_TAC ‘measure (λx. case x of
    INL (t, a, encoded) => cv_size a
  | INR (ts, vs, encoded, pos) => cv_size vs)’ >>
  cv_termination_tac
);

Theorem indexed_data_pre[cv_pre]:
  (∀t a encoded. indexed_data_pre t a encoded) ∧
  (∀ts vs encoded pos. indexed_parts_pre ts vs encoded pos)
Proof
  ho_match_mp_tac indexed_data_ind >> rpt strip_tac >>
  simp[Once indexed_data_pre_def] >> rw[] >> gvs[]
QED

val () = cv_auto_trans writes_end_def;
val inplace_partial_writes_pre_def = cv_auto_trans_pre_rec
  "inplace_partial_writes_pre inplace_parts_writes_pre" inplace_partial_writes_def (
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    INL (src, t, p) => (cv_size p, 0n)
  | INR (src, off, ts, done, q) => (cv_size q, cv_size ts + 1))’ >>
  cv_termination_tac
);

Theorem inplace_partial_writes_pre[cv_pre]:
  (∀src t p. inplace_partial_writes_pre src t p) ∧
  (∀src off ts done q. inplace_parts_writes_pre src off ts done q)
Proof
  ho_match_mp_tac inplace_partial_writes_ind >> rpt strip_tac >>
  simp[Once inplace_partial_writes_pre_def] >> rw[] >> gvs[]
QED
val () = cv_auto_trans runtime_abi_value_def;
val runtime_abi_values_pre_def =
  cv_auto_trans_pre "runtime_abi_values_pre" runtime_abi_values_def;

Theorem runtime_abi_values_pre[cv_pre,local]:
  ∀env reach st tys vs. runtime_abi_values_pre env reach st tys vs
Proof
  ho_match_mp_tac runtime_abi_values_ind >> rpt strip_tac >>
  simp[Once runtime_abi_values_pre_def] >> rw[] >> gvs[]
QED
val () = cv_auto_trans tuple_partial_writes_def;

val () = cv_auto_trans encoder_state_def;
val () = cv_auto_trans encoded_runtime_values_def;
val () = cv_auto_trans packed_value_def;
val packed_values_pre_def =
  cv_auto_trans_pre "packed_values_pre" packed_values_def;

Theorem packed_values_pre[cv_pre]:
  ∀env reach st tys vs. packed_values_pre env reach st tys vs
Proof
  ho_match_mp_tac packed_values_ind >> rpt strip_tac >>
  simp[Once packed_values_pre_def] >> rw[] >> gvs[]
QED

val () = cv_auto_trans packed_encoding_def;
val decode_memory_value_pre_def = cv_auto_trans_pre_rec
  "decode_memory_value_pre decode_memory_elements_pre decode_memory_fields_pre decode_memory_part_pre"
  decode_memory_value_def (
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (_, fuel, ty, _) => (cv$c2n fuel, cv_size ty, 1)
  | INR (INL (_, fuel, element, _, _, _, _, _, n, _)) =>
      (cv$c2n fuel, cv_size element, cv$c2n n + 3)
  | INR (INR (INL (_, fuel, tys, _))) =>
      (cv$c2n fuel, cv_size tys, 0)
  | INR (INR (INR (_, fuel, ty, _))) =>
      (cv$c2n fuel, cv_size ty, 2))’ >>
  cv_termination_tac
);

Theorem decode_memory_value_pre[cv_pre]:
  (∀env fuel ty bs total bound pos free reach.
     decode_memory_value_pre env fuel ty bs total bound pos free reach) ∧
  (∀env fuel element bs total bound data i n free reach.
     decode_memory_elements_pre env fuel element bs total bound data i n free reach) ∧
  (∀env fuel tys bs total bound base src free reach.
     decode_memory_fields_pre env fuel tys bs total bound base src free reach) ∧
  (∀env fuel ty bs total bound base src free reach.
     decode_memory_part_pre env fuel ty bs total bound base src free reach)
Proof
  ho_match_mp_tac decode_memory_value_ind >> rpt strip_tac >>
  simp[Once decode_memory_value_pre_def] >> rw[] >> gvs[]
QED
val () = cv_auto_trans copy_calldata_array_def;
val () = cv_auto_trans decode_abi_argument_def;
val () = cv_auto_trans decode_abi_arguments_def;
val () = cv_auto_trans decode_input_def;
val () = cv_auto_trans decode_arguments_def;
val materialize_value_pre_def = cv_auto_trans_pre_rec
  "materialize_value_pre materialize_words_pre" materialize_value_def (
  WF_REL_TAC ‘measure (λx. case x of
    INL (env, ty, v, st) => cv_size v
  | INR (env, tys, vs, p, st) => cv_size vs)’ >>
  cv_termination_tac
);

Theorem materialize_value_pre[cv_pre]:
  (∀env ty v st. materialize_value_pre env ty v st) ∧
  (∀env tys vs p st. materialize_words_pre env tys vs p st)
Proof
  ho_match_mp_tac materialize_value_ind >> rpt strip_tac >>
  simp[Once materialize_value_pre_def] >> rw[] >> gvs[]
QED

val materialize_storage_pre_def = cv_auto_trans_pre_rec
  "materialize_storage_pre materialize_storage_elements_pre materialize_storage_fields_pre"
  materialize_storage_def (
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<) (λx. case x of
    INL (env, fuel, accounts, addr, slot, ty, st) => (cv$c2n fuel, cv_size ty, 0)
  | INR (INL (env, fuel, accounts, addr, data, element, i, n, q, st)) =>
      (cv$c2n fuel, cv_size element, cv$c2n n + 1)
  | INR (INR (env, fuel, accounts, addr, slot, layout, fields, q, st)) =>
      (cv$c2n fuel, cv_size fields, 1))’ >>
  cv_termination_tac
);

Theorem materialize_storage_pre[cv_pre]:
  (∀env fuel accounts addr slot ty st.
     materialize_storage_pre env fuel accounts addr slot ty st) ∧
  (∀env fuel accounts addr data element i n q st.
     materialize_storage_elements_pre env fuel accounts addr data element i n q st) ∧
  (∀env fuel accounts addr slot layout fields q st.
     materialize_storage_fields_pre env fuel accounts addr slot layout fields q st)
Proof
  ho_match_mp_tac materialize_storage_ind >> rpt strip_tac >>
  simp[Once materialize_storage_pre_def] >> rw[] >> gvs[]
QED

val materialize_arguments_pre_def =
  cv_auto_trans_pre "materialize_arguments_pre" materialize_arguments_def;

Theorem materialize_arguments_pre[cv_pre]:
  ∀env tys vs st. materialize_arguments_pre env tys vs st
Proof
  ho_match_mp_tac materialize_arguments_ind >> rpt strip_tac >>
  simp[Once materialize_arguments_pre_def] >> rw[] >> fs[]
QED
val () = cv_auto_trans panic_data_def;

val () = cv_auto_trans write_at_each_def;
val () = cv_auto_trans
  (REWRITE_RULE [GSYM byteTheory.word_of_bytes_be_def] event_part_def);

val event_parts_pre_def = cv_auto_trans_pre "event_parts_pre" event_parts_def;

Theorem event_parts_pre[cv_pre,local]:
  ∀env reach st args. event_parts_pre env reach st args
Proof
  ho_match_mp_tac event_parts_ind >> rpt strip_tac >>
  simp[Once event_parts_pre_def] >> rw[] >> gvs[]
QED

val () = cv_auto_trans event_state_def;
val () = cv_auto_trans event_log_def;
