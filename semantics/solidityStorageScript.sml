(* Concrete storage interfaces shared by execution and observation. *)
Theory solidityStorage
Ancestors
  solidityState solidityScalar vfmCompute keccak
Libs
  cv_transLib wordsLib intLib

Datatype:
  value_outcome = ValueOk runtime_value | ValueAbrupt source_completion
End

(* Storage *)

(* A value as the number held in its b storage bytes: integers in two's
 * complement, fixed bytes big-endian.
 *)
Definition stored_number_def:
  stored_number b s =
    case s of
      BoolValue v => SOME (if v then 1 else 0)
    | IntegerValue i => SOME (Num (wrap_integer F (8 * b) i))
    | AddressValue a => SOME (w2n a)
    | BytesValue bs => SOME (num_of_be_bytes bs)
    | _ => NONE
End

(* The value of type ty held as the number n < 256 ** storage_bytes ty. *)
Definition stored_value_def:
  stored_value ty (n : num) =
    case ty of
      BoolT => SOME (BoolValue (n ≠ 0))
    | UintT _ => SOME (IntegerValue (&n))
    | IntT w => SOME (IntegerValue (wrap_integer T w (&n)))
    | AddressT _ => SOME (AddressValue (n2w n))
    | FixedBytesT k => SOME (BytesValue (num_to_bytes k n))
    | _ => NONE
End

(* The bytes of a value of type ty at a byte offset from the low-order end of
 * a slot of an account. Reading keeps only those bytes, as the compiler's
 * storage cleanup does; writing replaces only them.
 *)
Definition read_storage_def:
  read_storage accounts addr slot offset ty =
    case storage_bytes ty of
      SOME b =>
        stored_value ty
          ((w2n (lookup_storage slot (lookup_account addr accounts).storage)
            DIV 2 ** (8 * offset)) MOD 2 ** (8 * b))
    | NONE => NONE
End

Definition write_storage_def:
  write_storage accounts addr slot offset ty s =
    case storage_bytes ty of
      NONE => NONE
    | SOME b =>
        case stored_number b s of
          NONE => NONE
        | SOME v =>
            let account = lookup_account addr accounts in
            let w = w2n (lookup_storage slot account.storage) in
            let lo = 2 ** (8 * offset) in
            let hi = 2 ** (8 * (offset + b)) in
            let w' = w DIV hi * hi + v MOD 2 ** (8 * b) * lo + w MOD lo in
            SOME (update_account addr
                    (account with storage :=
                       update_storage slot (n2w w') account.storage)
                    accounts)
End

(* A declaration's concrete location in the executing account. *)
Definition state_reference_def:
  state_reference env addr (AstId x) =
    case lookup_state_variable env (AstId x) of
      SOME v => SOME (StorageReference PersistentStorage addr
        v.state_slot v.state_offset v.state_type (LayoutId x))
    | NONE => NONE
End

(* Solidity mapping keys occupy one 32-byte word: integers are extended to
 * 256 bits, addresses and booleans are zero padded, bytesN are right padded.
 *)
Definition mapping_key_bytes_def:
  mapping_key_bytes key s =
    if ¬elementary_storage_type_ok key ∨ ¬elementary_scalar_has_type key s then NONE
    else case s of
      BytesValue bs => SOME (bs ++ REPLICATE (32 - LENGTH bs) 0w)
    | _ => OPTION_MAP (num_to_bytes 32) (stored_number 32 s)
End

Definition mapping_slot_def:
  mapping_slot key_bytes (slot : bytes32) : bytes32 =
    word_of_bytes_be (Keccak_256_w64 (key_bytes ++ num_to_bytes 32 (w2n slot)))
End

(* One new index from a captured fixed-array reference. The caller has already
 * evaluated the index; slot arithmetic wraps at the EVM word width. *)
Definition fixed_array_element_def:
  fixed_array_element env addr slot element length layout (i : int) =
    if i < 0 ∨ &length ≤ i then ValueAbrupt (PanicCompletion 50) else
    case storage_bytes element of
      SOME b =>
        if b = 0 ∨ 32 < b then
          ValueAbrupt (InvalidCompletion "bad array element width")
        else
          let per_slot = 32 DIV b in
          ValueOk (ReferenceValue
            (StorageReference PersistentStorage addr
              (n2w (w2n slot + Num i DIV per_slot))
              (b * (Num i MOD per_slot)) element layout))
    | NONE =>
        case fixed_storage_slots env element of
          SOME slots =>
            ValueOk (ReferenceValue
              (StorageReference PersistentStorage addr
                (n2w (w2n slot + Num i * slots)) 0 element layout))
        | NONE => ValueAbrupt (InvalidCompletion "bad array element type")
End

(* Navigation consumes already evaluated atoms and returns a concrete location.
 * A nested mapping starts at the preceding mapping's hashed slot.
 *)
Definition navigate_storage_def:
  navigate_storage env accounts r s =
    case r of
      StorageReference PersistentStorage addr slot 0 (MappingT key value) layout =>
        (case mapping_key_bytes key s of
           SOME bs =>
             ValueOk (ReferenceValue
               (StorageReference PersistentStorage addr (mapping_slot bs slot)
                  0 value layout))
         | NONE => ValueAbrupt (InvalidCompletion "bad mapping key"))
    | StorageReference PersistentStorage addr slot 0
        (ArrayT element (SOME length)) layout =>
        (case s of
           IntegerValue i => fixed_array_element env addr slot element length layout i
         | _ => ValueAbrupt (InvalidCompletion "bad array index"))
    | StorageReference PersistentStorage addr slot 0 (ArrayT element NONE) layout =>
        (case s of
           IntegerValue i =>
             fixed_array_element env addr (mapping_slot [] slot) element
               (w2n (lookup_storage slot (lookup_account addr accounts).storage)) layout i
         | _ => ValueAbrupt (InvalidCompletion "bad array index"))
    | _ => ValueAbrupt (InvalidCompletion "unsupported storage navigation")
End

(* Access and navigation consume concrete references, independently of atoms,
 * bindings, scopes and evaluator control flow.
 *)
Definition read_storage_reference_def:
  read_storage_reference accounts ty r =
    case r of
      StorageReference PersistentStorage addr slot offset rty _ =>
        if rty ≠ ty then ValueAbrupt (InvalidCompletion "bad read type")
        else (case read_storage accounts addr slot offset ty of
                SOME scalar => ValueOk (ScalarValue scalar)
              | NONE => ValueAbrupt (InvalidCompletion "bad storage read"))
    | _ => ValueAbrupt (InvalidCompletion "bad storage reference")
End

Definition storage_array_length_def:
  storage_array_length accounts r =
    case r of
      StorageReference PersistentStorage addr slot 0 (ArrayT _ NONE) _ =>
        ValueOk (ScalarValue (IntegerValue
          (&(w2n (lookup_storage slot (lookup_account addr accounts).storage)))))
    | _ => ValueAbrupt (InvalidCompletion "bad dynamic array reference")
End

Definition navigate_storage_field_def:
  navigate_storage_field env r member_id =
    case r of
      StorageReference PersistentStorage addr slot 0 (StructT id) layout =>
        (case lookup_struct_layout env id of
           SOME s =>
             (case ALOOKUP (MAP (λv. (v.state_id, v)) s.struct_fields) member_id of
                SOME v => ValueOk (ReferenceValue
                  (StorageReference PersistentStorage addr (slot + v.state_slot)
                    v.state_offset v.state_type layout))
              | NONE => ValueAbrupt (InvalidCompletion "unknown struct field"))
         | NONE => ValueAbrupt (InvalidCompletion "missing struct layout"))
    | _ => ValueAbrupt (InvalidCompletion "bad struct reference")
End

(* Verifereum storage is a total function. Its canonical sparse cv encoding
 * omits zero entries, so encoding equality decides full extensional equality.
 *)
Theorem storage_encoding_injective:
  from_storage left = from_storage right ⇔ left = right
Proof
  metis_tac[vfmStateTheory.from_to_storage, cv_typeTheory.from_to_def]
QED

Theorem storage_equality_cv_rep[cv_rep]:
  b2c ((left : storage) = right) = cv_eq (from_storage left) (from_storage right)
Proof
  Cases_on ‘left = right’ >>
  simp[cvTheory.cv_eq_def, cvTheory.b2c_def, storage_encoding_injective]
QED

val () = cv_auto_trans read_storage_def;
val () = cv_auto_trans write_storage_def;
val () = cv_auto_trans state_reference_def;
val () = cv_auto_trans navigate_storage_def;
val () = cv_auto_trans read_storage_reference_def;
val () = cv_auto_trans storage_array_length_def;
val () = cv_auto_trans navigate_storage_field_def;
