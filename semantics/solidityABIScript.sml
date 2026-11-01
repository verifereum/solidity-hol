(* The ABI at the contract boundary, for elementary value types: calldata
 * arguments, return data, Panic(uint256) revert data and event logs, over
 * Verifereum's contractABI encoding.
 *)
Theory solidityABI
Ancestors
  contractABI
  (* for its cv encodings of runtime values and events, so that every
   * descendant sees one encoding *)
  solidityStorage
Libs
  cv_transLib wordsLib intLib

Definition abi_type_def:
  (abi_type (UintT n) = Uint n) ∧
  (abi_type (IntT n) = Int n) ∧
  (abi_type BoolT = Bool) ∧
  (abi_type (AddressT _) = Address) ∧
  (abi_type (FixedBytesT n) = Bytes (SOME n)) ∧
  (abi_type _ = Tuple [])
End

Definition abi_value_def:
  (abi_value (UintT _) (ScalarValue (IntegerValue i)) = SOME (NumV (Num i))) ∧
  (abi_value (IntT _) (ScalarValue (IntegerValue i)) = SOME (IntV i)) ∧
  (abi_value BoolT (ScalarValue (BoolValue b)) =
    SOME (NumV (if b then 1 else 0))) ∧
  (abi_value (AddressT _) (ScalarValue (AddressValue a)) =
    SOME (NumV (w2n a))) ∧
  (abi_value (FixedBytesT _) (ScalarValue (BytesValue bs)) = SOME (BytesV bs)) ∧
  (abi_value _ _ = NONE)
End

Definition abi_values_def:
  (abi_values [] [] = SOME []) ∧
  (abi_values (ty :: tys) (v :: vs) =
    case (abi_value ty v, abi_values tys vs) of
      (SOME a, SOME as) => SOME (a :: as)
    | _ => NONE) ∧
  (abi_values _ _ = NONE)
End

(* The encoding of values as a tuple of their types: return data. *)
Definition encoded_values_def:
  encoded_values tys vs =
    case abi_values tys vs of
      SOME avs => SOME (enc (Tuple (MAP abi_type tys)) (ListV avs))
    | NONE => NONE
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
  (abi_runtime_value _ _ = NONE)
End

Definition abi_runtime_values_def:
  (abi_runtime_values [] [] = SOME []) ∧
  (abi_runtime_values (ty :: tys) (a :: as) =
    case (abi_runtime_value ty a, abi_runtime_values tys as) of
      (SOME v, SOME vs) => SOME (v :: vs)
    | _ => NONE) ∧
  (abi_runtime_values _ _ = NONE)
End

(* Arguments decoded from calldata after the selector, NONE where the
 * compiler's decoder reverts: data too short for the head, or a word that is
 * not a clean value of its type. Extra trailing data is ignored.
 *)
Definition decode_arguments_def:
  decode_arguments tys bs =
    let t = Tuple (MAP abi_type tys) in
    if valid_enc t bs then
      case dec t bs of
        ListV avs => abi_runtime_values tys avs
      | _ => NONE
    else NONE
End

(* Revert data of Panic(uint256), selector 0x4e487b71. *)
Definition panic_data_def:
  panic_data n = [0x4Ew; 0x48w; 0x7Bw; 0x71w] ++ enc (Uint 256) (NumV n)
End

(* Event arguments split into the topics of the indexed ones, each the
 * value's ABI word, and the types and values of the rest, which form the
 * log's data.
 *)
Definition event_parts_def:
  (event_parts [] = SOME ([], [], [])) ∧
  (event_parts ((ty, indexed, v) :: args) =
    case (abi_value ty v, event_parts args) of
      (SOME a, SOME (topics, tys, avs)) =>
        if indexed then
          SOME ((word_of_bytes T (0w : bytes32) (enc (abi_type ty) a)) :: topics,
                tys, avs)
        else SOME (topics, abi_type ty :: tys, a :: avs)
    | _ => NONE)
End

Definition event_log_def:
  event_log logger topic0 args =
    case event_parts args of
      SOME (topics, tys, avs) =>
        SOME <| logger := logger;
                topics := (case topic0 of SOME t => t :: topics | NONE => topics);
                data := enc (Tuple tys) (ListV avs) |>
    | NONE => NONE
End

val () = cv_auto_trans abi_type_def;
val () = cv_auto_trans abi_value_def;
val () = cv_auto_trans abi_values_def;
val () = cv_auto_trans encoded_values_def;
val () = cv_auto_trans abi_runtime_value_def;
val () = cv_auto_trans abi_runtime_values_def;
val () = cv_auto_trans decode_arguments_def;
val () = cv_auto_trans panic_data_def;
val () = cv_auto_trans
  (REWRITE_RULE [GSYM byteTheory.word_of_bytes_be_def] event_parts_def);
val () = cv_auto_trans event_log_def;
