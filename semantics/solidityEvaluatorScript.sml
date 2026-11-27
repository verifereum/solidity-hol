(* Evaluator: locals, value-type state variables, control flow and internal
 * calls over the core, fuel-indexed by recursive depth.
 *
 * Fuel: statement-list traversal is structural and siblings reuse the bound;
 * invoke_source decrements on entry and a while loop decrements on its back
 * edge, so straight-line code and a loop's first iteration need none. No step
 * counter is threaded through the state.
 *
 * Scopes: an if branch and each loop iteration run in a pushed scope, and
 * leaving pops only that scope, so writes to enclosing bindings survive. A
 * procedure runs in a fresh scope and target map; the caller's are restored
 * afterwards, since the pure fragment has no references through which a callee
 * could reach them. Within a procedure, capturing a target overwrites it.
 *
 * Storage: a state variable lives in the storage of the executing account,
 * frame.self_address, in the world's verifereum accounts, at the slot and
 * byte offset of the program's layout. Reads and writes go straight to that
 * world, so a write is seen by everything after it, callers and callees
 * included; restoring the world on revert is the frame's job
 * (finish_source_frame). Access sets are not tracked. The world also
 * carries the transaction's original accounts and pending deletions, which
 * the evaluator only threads through the message calls and creations it
 * hands to Verifereum (externalCallScript.sml).
 *
 * Gas evidence is passed through unchanged; the EVM boundary is out of scope.
 * Unsupported statements and operations, and anything the checker would reject,
 * end in InvalidCompletion.
 *)
Theory solidityEvaluator
Ancestors
  solidityMemory solidityABI externalCall yulEvaluator
Libs
  cv_transLib wordsLib intLib

(* Scopes and targets *)

Definition ast_key_def:
  ast_key (AstId n) = n
End

Definition lookup_binding_def:
  (lookup_binding x [] = NONE) ∧
  (lookup_binding x (scope :: scopes) =
    case FLOOKUP scope (ast_key x) of
      SOME b => SOME b
    | NONE => lookup_binding x scopes)
End

(* Writes the binding in the innermost scope that holds it. *)
Definition update_binding_def:
  (update_binding x v [] = NONE) ∧
  (update_binding x v (scope :: scopes) =
    case FLOOKUP scope (ast_key x) of
      SOME b =>
        SOME ((scope |+ (ast_key x, b with binding_value := v)) :: scopes)
    | NONE =>
        (case update_binding x v scopes of
           SOME scopes' => SOME (scope :: scopes')
         | NONE => NONE))
End

Definition bind_local_def:
  (bind_local x b [] = [FEMPTY |+ (ast_key x, b)]) ∧
  (bind_local x b (scope :: scopes) = (scope |+ (ast_key x, b)) :: scopes)
End

Definition set_target_def:
  set_target t target targets = targets |+ (ast_key t, target)
End

Definition push_scope_def:
  push_scope (st : source_state) = st with scopes := FEMPTY :: st.scopes
End

Definition pop_scopes_def:
  (pop_scopes [] = []) ∧
  (pop_scopes (_ :: scopes) = scopes)
End

(* Results *)

Definition normal_result_def:
  normal_result st gas =
    <| completion := NormalCompletion; state := st;
       unused_gas_evidence := gas |>
End

(* The memory a completion leaves: the compiler's panic_error_<code> writes
 * the Panic selector and code to scratch, mstore(0, selector) then
 * mstore(4, code), before revert(0, 0x24). *)
Definition completion_memory_def:
  completion_memory c st =
    case c of
      PanicCompletion code => memory_write 0 (panic_data code) st
    | _ => st
End

Definition abrupt_result_def:
  abrupt_result c st gas =
    <| completion := c; state := completion_memory c st;
       unused_gas_evidence := gas |>
End

Definition pop_result_def:
  pop_result (r : source_result) =
    r with state := (r.state with scopes := pop_scopes r.state.scopes)
End

(* Atoms and pure operations *)

Definition eval_atom_def:
  (eval_atom scopes (ConstantAtom s) = SOME (ScalarValue s)) ∧
  (eval_atom scopes (BoundAtom x) =
    case lookup_binding x scopes of
      SOME b => SOME b.binding_value
    | NONE => NONE)
End

Definition eval_atoms_def:
  (eval_atoms scopes [] = SOME []) ∧
  (eval_atoms scopes (a :: atoms) =
    case (eval_atom scopes a, eval_atoms scopes atoms) of
      (SOME v, SOME vs) => SOME (v :: vs)
    | _ => NONE)
End

Definition scalar_values_def:
  (scalar_values [] = SOME []) ∧
  (scalar_values (ScalarValue s :: vs) =
    case scalar_values vs of SOME ss => SOME (s :: ss) | NONE => NONE) ∧
  (scalar_values (_ :: _) = NONE)
End

(* The source type of a conversion: a binding's declared type, or the target
 * type for a constant (the literal/default-initialisation form).
 *)
Definition conversion_source_type_def:
  (conversion_source_type scopes ty (ConstantAtom _) = SOME ty) ∧
  (conversion_source_type scopes ty (BoundAtom x) =
    case lookup_binding x scopes of
      SOME b =>
        (case b.binding_type of SingleType src => SOME src | _ => NONE)
    | NONE => NONE)
End

Definition scalar_outcome_value_def:
  scalar_outcome_value (ScalarOk s) = ValueOk (ScalarValue s) ∧
  scalar_outcome_value (ScalarPanic code) = ValueAbrupt (PanicCompletion code) ∧
  scalar_outcome_value ScalarInvalid =
    ValueAbrupt (InvalidCompletion "ill-typed scalar operands")
End

(* Operations over scalar values and tuples, without storage access. *)
Definition eval_pure_operation_def:
  eval_pure_operation env scopes op =
    case op of
      ScalarOperation ty mode oper atoms =>
        (case eval_atoms scopes atoms of
           NONE =>
             ValueAbrupt (InvalidCompletion "unbound atom")
         | SOME vs =>
             (case scalar_values vs of
                NONE => ValueAbrupt (InvalidCompletion "non-scalar operand")
              | SOME ss =>
                  scalar_outcome_value
                    (eval_scalar_operation env ty mode oper ss)))
    | ConvertOperation ty a =>
        (case (conversion_source_type scopes ty a, eval_atom scopes a) of
           (SOME src, SOME (ScalarValue s)) =>
             scalar_outcome_value (eval_conversion env src ty s)
         | (SOME src, SOME (ReferenceValue r)) =>
             if src = ty then ValueOk (ReferenceValue r)
             else convert_byte_reference src ty r
         | _ => ValueAbrupt (InvalidCompletion "ill-typed conversion"))
    | TupleOperation atoms =>
        (case eval_atoms scopes atoms of
           SOME vs => ValueOk (TupleValue vs)
         | NONE =>
             ValueAbrupt (InvalidCompletion "unbound atom"))
    | TupleComponentOperation n a =>
        (case eval_atom scopes a of
           SOME (TupleValue vs) =>
             (case oEL n vs of
                SOME v => ValueOk v
              | NONE => ValueAbrupt (InvalidCompletion "tuple index"))
         | _ => ValueAbrupt (InvalidCompletion "not a tuple"))
    | _ => ValueAbrupt (InvalidCompletion "unsupported operation")
End

Definition default_scalar_def:
  default_scalar env ty =
    case ty of
      EnumT _ => SOME (IntegerValue 0)
    | UserValueT id =>
        (case lookup_user_value env id of
           SOME u => default_elementary u
         | NONE => NONE)
    | _ => default_elementary ty
End

(* A static memory array return binding starts at the zero slot too; the
 * elaborated body allocates its zero value before running. The compiler
 * rejects reading a calldata return binding before it is assigned, so its
 * default is never observed. *)
Definition default_runtime_value_def:
  default_runtime_value env ty =
    case ty of
      LocatedT MemoryLoc element =>
        if located_type_ok env MemoryLoc element then
          SOME (ReferenceValue (MemoryReference 96 element))
        else NONE
    | LocatedT CalldataLoc element =>
        if located_type_ok env CalldataLoc element then
          SOME (ReferenceValue (CalldataReference 0
            (case element of ArrayT _ (SOME n) => n | _ => 0) element))
        else NONE
    | LocatedT StorageLoc element =>
        if located_type_ok env StorageLoc element then
          SOME (ReferenceValue
            (StorageReference PersistentStorage 0w 0w 0 element (LayoutId 0)))
        else NONE
    | _ => OPTION_MAP ScalarValue (default_scalar env ty)
End

(* msg, this, tx and block reads, from the frame. *)
(* The numeric fields are unbounded in the frame; the EVM reads each as a
 * word, so as a uint256 it wraps.
 *)
Definition environment_value_def:
  environment_value (fr : source_frame) f =
    case f of
      MsgData => ValueOk (ReferenceValue (CalldataReference 0 (LENGTH fr.call_data) BytesT))
    | MsgSig => ValueOk (ScalarValue (BytesValue (TAKE 4 (fr.call_data ++ REPLICATE 4 0w))))
    | MsgSender => ValueOk (ScalarValue (AddressValue fr.sender_address))
    | MsgValue =>
        ValueOk (ScalarValue (IntegerValue (wrap_integer F 256 (&fr.call_value))))
    | SelfAddress => ValueOk (ScalarValue (AddressValue fr.self_address))
    | TxOrigin => ValueOk (ScalarValue (AddressValue fr.tx_params.origin))
    | TxGasPrice =>
        ValueOk (ScalarValue (IntegerValue (wrap_integer F 256 (&fr.tx_params.gasPrice))))
    | BlockNumber =>
        ValueOk (ScalarValue (IntegerValue (wrap_integer F 256 (&fr.tx_params.blockNumber))))
    | BlockTimestamp =>
        ValueOk (ScalarValue (IntegerValue (wrap_integer F 256 (&fr.tx_params.blockTimeStamp))))
    | BlockChainId =>
        ValueOk (ScalarValue (IntegerValue (wrap_integer F 256 (&fr.tx_params.chainId))))
    | BlockCoinbase => ValueOk (ScalarValue (AddressValue fr.tx_params.blockCoinBase))
    | BlockBaseFee =>
        ValueOk (ScalarValue (IntegerValue (wrap_integer F 256 (&fr.tx_params.baseFeePerGas))))
    | BlockBlobBaseFee =>
        ValueOk (ScalarValue (IntegerValue (wrap_integer F 256 (&fr.tx_params.baseFeePerBlobGas))))
    | BlockGasLimit =>
        ValueOk (ScalarValue (IntegerValue (wrap_integer F 256 (&fr.tx_params.blockGasLimit))))
    | BlockPrevRandao => ValueOk (ScalarValue (IntegerValue (&w2n fr.tx_params.prevRandao)))
    | GasLeft => ValueAbrupt (InvalidCompletion "missing gasleft observation")
End

(* A call's value, following call_result_type: nothing, one value, or a tuple. *)
Definition pack_results_def:
  (pack_results [] = TupleValue []) ∧
  (pack_results [v] = v) ∧
  (pack_results vs = TupleValue vs)
End

(* A byte of a fixed or dynamic byte sequence, in source order. *)
Definition indexed_byte_def:
  indexed_byte bs i =
    if i < 0 ∨ &(LENGTH bs) ≤ i then ValueAbrupt (PanicCompletion 50)
    else case oEL (Num i) bs of
      SOME b => ValueOk (ScalarValue (BytesValue [b]))
    | NONE => ValueAbrupt (InvalidCompletion "bad byte index")
End

(* A byte sequence (a literal, or one in memory, calldata or storage) packed
 * at the free memory pointer, as the compiler packs sha256's operand and a
 * low-level call's data other than a memory byte sequence; the pointer is not
 * moved. *)
Definition packed_call_data_def:
  packed_call_data (st : source_state) d =
    case (case d of
            ReferenceValue r => byte_contents st r
          | ScalarValue (BytesValue bs) => INL (bs, st)
          | _ => INR (InvalidCompletion "bad packed byte sequence")) of
      INL (bs, st1) =>
        let (p, st2) = memory_load 64 st1 in
        INL (bs, memory_write p (bs ++ packed_bytes_tail st2.world.accounts d bs) st2)
    | INR c => INR c
End

(* The gas a high-level call gives its callee. The source does not track gas,
 * where the bytecode passes all but a 64th of what it has left.
 *)
Definition external_call_gas_def:
  external_call_gas = 10000000n
End

(* The 32-byte word ERC-7201's runtime helper writes at scratch 0. *)
Definition erc7201_preimage_def:
  erc7201_preimage bs =
    word_to_bytes ((word_of_bytes_be (Keccak_256_w64 bs) : bytes32) - 1w) T
End

(* The namespace slot for the preimage, with the low byte cleared. *)
Definition erc7201_slot_def:
  erc7201_slot preimage =
    w2n (word_and (word_of_bytes_be (Keccak_256_w64 preimage) : bytes32)
                 (word_1comp 0xffw))
End

(* A builtin's value on its operands' values, and the state after it, with
 * the memory the compiler's code uses for it. keccak256 hashes the bytes in
 * place. sha256, ripemd160 and ecrecover use precompile output at scratch 0
 * on an encoding at the unchanged free memory pointer (sha256 and ripemd160
 * use packed_call_data):
 * ecrecover zeroes it first, as an invalid signature returns nothing, which
 * reads as address(0), and the precompile reads its input from memory after
 * that. a.code allocates memory bytes and copies the code there. *)
Definition eval_builtin_def:
  eval_builtin st op vs =
    case (op, vs) of
      (Keccak256Builtin, [ReferenceValue r]) =>
        (case byte_contents st r of
           INL (bs, st1) => INL (ScalarValue (BytesValue (num_to_bytes 32
                       (w2n (word_of_bytes_be (Keccak_256_w64 bs) : bytes32)))), st1)
         | INR c => INR c)
    | (EcrecoverBuiltin,
       [ScalarValue (BytesValue hb); ScalarValue (IntegerValue vi);
        ScalarValue (BytesValue rb); ScalarValue (BytesValue sb)]) =>
        let (p, st1) = memory_load 64 st in
        let st2 = memory_write p (hb ++ num_to_bytes 32 (Num vi) ++ rb ++ sb) st1 in
        let st3 = memory_store 0 0 st2 in
        let input = FST (memory_read p 128 st3) in
        let result = ecrecover (word_of_bytes_be (TAKE 32 input))
                       (num_of_be_bytes (TAKE 32 (DROP 32 input)))
                       (num_of_be_bytes (TAKE 32 (DROP 64 input)))
                       (num_of_be_bytes (DROP 96 input)) in
        INL (ScalarValue (AddressValue (case result of SOME a => a | NONE => 0w)),
             case result of
               SOME a => memory_store 0 (w2n a) st3
             | NONE => st3)
    | (CodeLengthBuiltin, [ScalarValue (AddressValue address)]) =>
        INL (ScalarValue (IntegerValue
          (&(LENGTH (lookup_account address st.world.accounts).code))), st)
    | (BalanceBuiltin, [ScalarValue (AddressValue address)]) =>
        INL (ScalarValue (IntegerValue
          (&(lookup_account address st.world.accounts).balance)), st)
    | (CodeHashBuiltin, [ScalarValue (AddressValue address)]) =>
        INL (ScalarValue (BytesValue (num_to_bytes 32
          (w2n (ext_code_hash st.world.accounts address)))), st)
    | (Sha256Builtin, [v]) =>
        (case packed_call_data st v of
           INL (bs, st1) =>
             let hash = num_to_bytes 32 (w2n (SHA_256_bytes bs)) in
             INL (ScalarValue (BytesValue hash), memory_write 0 hash st1)
         | INR c => INR c)
    | (Ripemd160Builtin, [v]) =>
        (case packed_call_data st v of
           INL (bs, st1) =>
             (case run_external_call st1.frame.self_address 3w bs 0 T external_call_gas
                     st1.world.accounts st1.world.original st1.world.transient
                     st1.frame.tx_params of
                SOME r =>
                  if r.call_success ∧ LENGTH r.call_return = 32 then
                    INL (ScalarValue (BytesValue (DROP 12 r.call_return)),
                         memory_write 0 r.call_return
                           (st1 with return_data := SOME r.call_return))
                  else INR (InvalidCompletion "ripemd160 precompile did not return a digest")
              | NONE => INR (InvalidCompletion "ripemd160 precompile call outside the model"))
         | INR c => INR c)
    | (Erc7201Builtin, [ReferenceValue r]) =>
        (case byte_contents st r of
           INL (bs, st1) =>
             let preimage = erc7201_preimage bs in
             INL (ScalarValue (IntegerValue (&(erc7201_slot preimage))),
                  memory_write 0 preimage st1)
         | INR c => INR c)
    | (BlobhashBuiltin, [ScalarValue (IntegerValue n)]) =>
        INL (ScalarValue (BytesValue
          (word_to_bytes (blob_hash_word st.frame.tx_params (Num n)) T)), st)
    | (BlockhashBuiltin, [ScalarValue (IntegerValue n)]) =>
        INL (ScalarValue (BytesValue (num_to_bytes 32
          (w2n (block_hash_word st.frame.tx_params (Num n))))), st)
    | (CodeBuiltin, [ScalarValue (AddressValue address)]) =>
        let code = (lookup_account address st.world.accounts).code in
        (case allocate_byte_array (LENGTH code) st of
           INL (p, st1) =>
             INL (ReferenceValue (MemoryReference p BytesT), memory_write (p + 32) code st1)
         | INR c => INR c)
    | _ => INR (InvalidCompletion "bad builtin operands")
End

(* Builtins whose precompile call is modelled without retaining returndata.
 * Calls through the external adapter carry their returndata in eval_builtin. *)
Definition builtin_calls_precompile_def:
  builtin_calls_precompile b ⇔ b = EcrecoverBuiltin ∨ b = Sha256Builtin
End

(* A value outcome as an operation's result, the state unchanged. *)
Definition outcome_result_def:
  outcome_result st r =
    case r of
      ValueOk v => INL (v, st)
    | ValueAbrupt c => INR c
End

(* A storage navigation step, with the scratch words solc writes for it. *)
Definition navigate_result_def:
  navigate_result env r s st =
    case navigate_storage env st.world.accounts r s of
      ValueOk v =>
        INL (v, memory_write 0 (navigation_scratch env st.world.accounts r s) st)
    | ValueAbrupt c => INR c
End

(* A constructor keeps the contract's immutables in its reserved memory,
 * a word each from 0x80, in declaration order, base contracts first. *)
Definition immutable_offset_def:
  (immutable_offset (x : ast_id) [] = NONE) ∧
  (immutable_offset x ((y, ty) :: rest) =
    if x = y then SOME (128 : num, ty : sol_type) else
    case immutable_offset x rest of
      SOME (a, t) => SOME (a + 32, t)
    | NONE => NONE)
End

(* A byte sequence mapping key's hash preimage, as the compiler's
 * packed_hashed writes it: the key's bytes, then the slot, at the free memory
 * pointer, which is not raised. *)
Definition key_preimage_write_def:
  key_preimage_write bs slot st =
    let (p, st1) = memory_load 64 st in
    memory_store (p + LENGTH bs) (w2n slot) (memory_write p bs st1)
End


(* Operations without nested code, and the state after them: reading memory
 * raises its active size. Calls and array mutations are handled by
 * statements. *)
Definition eval_operation_def:
  eval_operation env (st : source_state) op =
    case op of
      DefaultReferenceOperation loc ty =>
        (case default_runtime_value env (LocatedT loc ty) of
           SOME v => INL (v, st)
         | NONE => INR (InvalidCompletion "bad reference default"))
    | StateReferenceOperation x =>
        (case state_reference env st.frame.self_address x of
           SOME r => INL (ReferenceValue r, st)
         | _ => INR (InvalidCompletion "bad state reference"))
    | ImmutableReferenceOperation x =>
        if IS_SOME (ALOOKUP env.immutables x)
        then INL (ReferenceValue (ImmutableReference x), st)
        else INR (InvalidCompletion "bad immutable reference")
    | StorageSlotOperation ty a =>
        (case eval_atom st.scopes a of
           SOME (ReferenceValue (StorageReference PersistentStorage owner slot 0 actual _)) =>
             if owner = st.frame.self_address ∧ actual = ty then
               INL (ScalarValue (IntegerValue (&(w2n slot))), st)
             else INR (InvalidCompletion "bad storage slot reference")
         | _ => INR (InvalidCompletion "bad storage slot reference"))
    | ReadOperation ty a =>
        (case eval_atom st.scopes a of
           SOME (ReferenceValue (MemoryReference p rty)) =>
             if ty = FixedBytesT 1 ∧ rty = ty then read_result (read_memory_word env ty p st)
             else INR (InvalidCompletion "bad memory read type")
         | SOME (ReferenceValue (MemoryWordReference p rty)) =>
             if (case ty of LocatedT MemoryLoc t => t | t => t) = rty
             then read_result (read_memory_word env rty p st)
             else INR (InvalidCompletion "bad memory read type")
         | SOME (ReferenceValue (CalldataReference head n rty)) =>
             if (case ty of LocatedT _ t => t | t => t) ≠ rty then
               INR (InvalidCompletion "bad calldata reference")
             else if is_stored_scalar_type rty then
               (case calldata_part env st.frame.call_data rty head head of
                  INL v => INL (v, st)
                | INR c => INR c)
             else INL (ReferenceValue (CalldataReference head n rty), st)
         | SOME (ReferenceValue (ImmutableReference x)) =>
             (case st.immutables of
                NONE =>
                  (case immutable_offset x env.immutables of
                     SOME (p, ity) => read_result (read_memory_word env ity p st)
                   | NONE => INR (InvalidCompletion "bad immutable reference"))
              | SOME imm =>
                  case FLOOKUP imm (ast_key x) of
                    SOME s => INL (ScalarValue s, st)
                  | NONE =>
                      case default_elementary ty of
                        SOME s => INL (ScalarValue s, st)
                      | NONE => INR (InvalidCompletion "bad immutable type"))
         | SOME (ReferenceValue r) => outcome_result st (read_storage_reference env st.world ty r)
         | _ => INR (InvalidCompletion "bad storage reference"))
    (* convert_bytes_to_fixedbytes: a memory byte sequence's length word and
     * its first data word, a long storage one's first data slot. *)
    | BytesToFixedOperation k a =>
        if ¬valid_fixed_bytes_width k then
          INR (InvalidCompletion "bad fixed bytes width") else
        (case eval_atom st.scopes a of
           SOME (ReferenceValue (MemoryReference p ty)) =>
             if ¬byte_sequence_type ty then INR (InvalidCompletion "bad bytes conversion operand")
             else
               let (n, st1) = memory_load p st in
               let (w, st2) = memory_load (p + 32) st1 in
               INL (ScalarValue (BytesValue (take_pad_0 k (TAKE n (num_to_bytes 32 w)))), st2)
         | SOME (ReferenceValue r) =>
             (case (case r of
                 StorageReference PersistentStorage addr slot 0 ty _ =>
                   if ¬byte_sequence_type ty then
                     INR (InvalidCompletion "not storage bytes")
                   else (case storage_byte_length st.world.accounts addr slot of
                     INR c => INR c
                   | INL length => INL (storage_byte_range
                       st.world.accounts addr slot length 0 (MIN k length),
                       scratch_write (long_bytes_scratch st.world.accounts addr slot) st))
               | _ => byte_contents st r) of
                INL (bs, st1) => INL (ScalarValue (BytesValue (take_pad_0 k bs)), st1)
              | INR c => INR c)
         | _ => INR (InvalidCompletion "bad bytes conversion operand"))
    | ArrayIndexOperation a index =>
        (case (eval_atom st.scopes a, eval_atom st.scopes index) of
           (SOME value, SOME (ScalarValue (IntegerValue i))) =>
             (case value of
                ScalarValue (BytesValue bs) => outcome_result st (indexed_byte bs i)
              | ReferenceValue r =>
                (case r of
                   StorageReference _ _ _ _ ty _ =>
                     (case indexed_element_type (LocatedT StorageLoc ty) of
                        SOME element =>
                          (case navigate_result env r (IntegerValue i) st of
                             INL (ReferenceValue r', st1) =>
                               outcome_result st1 (read_storage_reference env st1.world
                                 (case element of LocatedT _ t => t | _ => element) r')
                           | INR c => INR c
                           | _ => INR (InvalidCompletion "bad storage array element"))
                      | NONE => INR (InvalidCompletion "bad indexed storage type"))
                 | CalldataReference data n (ArrayT element _) =>
                     if i < 0 ∨ &n ≤ i then INR (PanicCompletion 50) else
                     (case calldata_part env st.frame.call_data element data
                             (data + Num i * abi_stride env element) of
                        INL v => INL (v, st)
                      | INR c => INR c)
                 | MemoryReference p (ArrayT element length) =>
                     (case memory_array_element (ArrayT element length) p i st of
                        INL (q, element, st1) => read_result (read_memory_word env element q st1)
                      | INR c => INR c)
                 | MemoryReference p ty =>
                     if ¬byte_sequence_type ty then INR (InvalidCompletion "bad indexed value")
                     else (case memory_byte_element p i st of
                        INL (q, st1) => read_result (read_memory_word env (FixedBytesT 1) q st1)
                      | INR c => INR c)
                 | _ =>
                     case byte_contents st r of
                       INL (bs, st1) => outcome_result st1 (indexed_byte bs i)
                     | INR c => INR c)
              | _ => INR (InvalidCompletion "bad indexed value"))
         | _ => INR (InvalidCompletion "bad array index operands"))
    | CalldataSliceOperation a start end_bound =>
        (case (eval_atom st.scopes a, eval_atom st.scopes start) of
           (SOME (ReferenceValue (CalldataReference offset length ty)),
            SOME (ScalarValue (IntegerValue first))) =>
             let last = case end_bound of
               NONE => SOME (ScalarValue (IntegerValue (&length)))
             | SOME b => eval_atom st.scopes b in
             (case last of
                SOME (ScalarValue (IntegerValue stop)) =>
                  if first < 0 ∨ stop < first ∨ &length < stop
                  then INR (RevertCompletion []) else
                  let stride = case ty of ArrayT element NONE => abi_stride env element | _ => 1 in
                  INL (ReferenceValue (CalldataReference
                    (offset + Num first * stride) (Num (stop - first)) ty), st)
              | _ => INR (InvalidCompletion "bad calldata slice end"))
         | _ => INR (InvalidCompletion "bad calldata slice operands"))
    | ArrayLengthOperation a =>
        (case eval_atom st.scopes a of
           SOME (ReferenceValue r) =>
             (case r of
                StorageReference _ _ _ _ _ _ =>
                  outcome_result st (storage_array_length st.world.accounts r)
              | MemoryReference p ty =>
                  if (case ty of ArrayT _ _ => T | _ => byte_sequence_type ty) then
                    let (n, st1) = memory_length ty p st in
                    INL (ScalarValue (IntegerValue (&n)), st1)
                  else INR (InvalidCompletion "bad memory array reference")
              | CalldataReference _ n _ => INL (ScalarValue (IntegerValue (&n)), st)
              | _ => case byte_contents st r of
                       INL (bs, st1) => INL (ScalarValue (IntegerValue (&(LENGTH bs))), st1)
                     | INR c => INR c)
         | _ => INR (InvalidCompletion "bad array reference"))
    | NavigateOperation ty root_expr (FieldNavigation member_id) =>
        (case eval_atom st.scopes root_expr of
           SOME (ReferenceValue (MemoryReference p (StructT s))) =>
             (case memory_struct_field env s p member_id of
                INL (q, fty) => INL (ReferenceValue (MemoryWordReference q fty), st)
              | INR c => INR c)
         | SOME (ReferenceValue (CalldataReference pos _ (StructT s))) =>
             (case calldata_struct_field env st.frame.call_data s pos member_id of
                INL v => INL (v, st)
              | INR c => INR c)
         | SOME (ReferenceValue r) => outcome_result st (navigate_storage_field env r member_id)
         | _ => INR (InvalidCompletion "bad struct reference"))
    | NavigateOperation ty root_expr (IndexNavigation index) =>
        (case (eval_atom st.scopes root_expr, eval_atom st.scopes index) of
           (SOME (ReferenceValue (MemoryReference p rty)),
            SOME (ScalarValue (IntegerValue i))) =>
             if rty ≠ BytesT then INR (InvalidCompletion "bad memory byte array") else
             (case memory_byte_element p i st of
                INL (q, st1) => INL (ReferenceValue (MemoryReference q (FixedBytesT 1)), st1)
              | INR c => INR c)
         (* packed_hashed: a byte sequence key's bytes, then the slot, at the
          * free memory pointer, which is not raised; a literal key too *)
         | (SOME (ReferenceValue (StorageReference PersistentStorage addr slot 0
                   (MappingT key value) layout)), SOME (ScalarValue (BytesValue bs))) =>
             navigate_result env
               (StorageReference PersistentStorage addr slot 0 (MappingT key value) layout)
               (BytesValue bs)
               (if byte_sequence_type key then key_preimage_write bs slot st else st)
         | (SOME (ReferenceValue r), SOME (ScalarValue s)) =>
             navigate_result env r s st
         | (SOME (ReferenceValue (StorageReference PersistentStorage addr slot 0
                   (MappingT key value) layout)), SOME (ReferenceValue key_ref)) =>
             if ¬byte_sequence_type key then
               INR (InvalidCompletion "bad mapping key")
             else (case byte_contents st key_ref of
                INL (bs, st1) =>
                  navigate_result env
                    (StorageReference PersistentStorage addr slot 0 (MappingT key value) layout)
                    (BytesValue bs) (key_preimage_write bs slot st1)
              | INR c => INR c)
         | _ => INR (InvalidCompletion "bad index operands"))
    | EnvironmentOperation f =>
        outcome_result st (environment_value st.frame f)
    | _ => outcome_result st (eval_pure_operation env st.scopes op)
End

(* Procedures *)

Definition single_binding_def:
  single_binding ty v = <| binding_type := SingleType ty; binding_value := v |>
End

Definition bind_parameters_def:
  (bind_parameters [] [] = SOME FEMPTY) ∧
  (bind_parameters ((x, ty) :: params) (v :: vs) =
    case bind_parameters params vs of
      SOME scope => SOME (scope |+ (ast_key x, single_binding ty v))
    | NONE => NONE) ∧
  (bind_parameters _ _ = NONE)
End

Definition bind_defaults_def:
  (bind_defaults env [] = SOME FEMPTY) ∧
  (bind_defaults env ((x, ty) :: rets) =
    case (default_runtime_value env ty, bind_defaults env rets) of
      (SOME s, SOME scope) =>
        SOME (scope |+ (ast_key x, single_binding ty s))
    | _ => NONE)
End

(* Parameters bound to arguments, return bindings default-initialised. *)
Definition entry_scope_def:
  entry_scope env (p : core_procedure) args =
    case (bind_parameters p.parameters args, bind_defaults env p.return_bindings)
    of
      (SOME params, SOME rets) => SOME (FUNION params rets)
    | _ => NONE
End

Definition read_returns_def:
  (read_returns scopes [] = SOME []) ∧
  (read_returns scopes ((x, _) :: rets) =
    case (eval_atom scopes (BoundAtom x), read_returns scopes rets) of
      (SOME v, SOME vs) => SOME (v :: vs)
    | _ => NONE)
End

(* Statements that do not run nested code *)

Definition define_binding_def:
  define_binding x ty v (st : source_state) =
    st with scopes :=
      bind_local x <| binding_type := ty; binding_value := v |> st.scopes
End

(* A storage write in a static frame fails; the EVM would halt exceptionally,
 * which no source completion models yet. An immutable is assigned only during
 * creation, in its reserved word.
 *)
Definition write_target_value_def:
  write_target_value env t v (st : source_state) =
    case (FLOOKUP st.targets (ast_key t), v) of
      (SOME (BindTarget x), v) =>
        (case update_binding x v st.scopes of
           SOME scopes => SOME (st with scopes := scopes)
         | NONE => NONE)
    | (SOME (ValueTarget (MemoryReference a ty)), ScalarValue (BytesValue [b])) =>
        if ty = FixedBytesT 1 then SOME (memory_write a [b] st) else NONE
    | (SOME (ValueTarget (MemoryWordReference a ty)), v) =>
        (case write_memory_word env ty a v st of
           INL st1 => SOME st1
         | INR _ => NONE)
    | (SOME (ValueTarget (ImmutableReference x)), ScalarValue s) =>
        (case (st.immutables, immutable_offset x env.immutables) of
           (NONE, SOME (a, ty)) =>
             (case write_memory_word env ty a (ScalarValue s) st of
                INL st1 => SOME st1
              | INR _ => NONE)
         | _ => NONE)
    | (SOME (ValueTarget (StorageReference PersistentStorage addr slot offset
                            ty _)), ScalarValue s) =>
        if st.frame.static_context then NONE else
        (case write_storage st.world.accounts addr slot offset ty s of
           SOME accounts =>
             SOME (st with world := st.world with accounts := accounts)
         | NONE => NONE)
    | (SOME (ValueTarget (StorageReference TransientStorage addr slot offset
                            ty _)), ScalarValue s) =>
        if st.frame.static_context then NONE else
        let storage = lookup_transient_storage addr st.world.transient in
        (case write_storage_word (lookup_storage slot storage) offset ty s of
           SOME word => SOME (st with world := st.world with transient :=
             update_transient_storage addr (update_storage slot word storage) st.world.transient)
         | NONE => NONE)
    | _ => NONE
End

Definition write_target_def:
  write_target env t a st =
    case eval_atom st.scopes a of
      SOME v => write_target_value env t v st
    | NONE => NONE
End

(* A memory variable is reset by rebinding it to a new zero value, so aliases
 * retain their contents; a memory word (an array element or struct field)
 * gets the zero value's word. Storage references clear in place, using the
 * same rule as array pop. *)
Definition reset_target_def:
  reset_target n env t ty (st : source_state) gas =
    case FLOOKUP st.targets (ast_key t) of
      SOME (ValueTarget (StorageReference PersistentStorage addr slot offset stored_ty _)) =>
        if st.frame.static_context then
          abrupt_result (InvalidCompletion "storage reset in static frame") st gas
        else
          (case clear_storage_value env (n + LENGTH env.type_declarations)
                  st.world.accounts addr slot offset stored_ty of
             INL (accounts, scratch) =>
               normal_result (scratch_write scratch
                 (st with world := st.world with accounts := accounts)) gas
           | INR c => abrupt_result c st gas)
    | _ =>
        let zero =
          case ty of
            LocatedT MemoryLoc element =>
              (case zero_value env (LENGTH env.type_declarations) element st of
                 INL (p, st1) => INL (ReferenceValue (MemoryReference p element), st1)
               | INR c => INR c)
          | _ =>
              (case default_scalar env ty of
                 SOME v => INL (ScalarValue v, st)
               | NONE => INR (InvalidCompletion "bad reset type")) in
        case zero of
          INR c => abrupt_result c st gas
        | INL (v, st') =>
            case write_target_value env t v st' of
              SOME st'' => normal_result st'' gas
            | NONE => abrupt_result (InvalidCompletion "bad reset target") st gas
End

(* The pinned profile checks push against 2^64, independently of source
 * arithmetic mode. push() preserves existing bytes at the appended location.
 * Update length before the value write, including in the presence of slot
 * collisions; pop clears the element before updating length. A byte array
 * pushes and pops as solc's byte array functions do (solidityStorage). *)
Definition push_storage_array_def:
  push_storage_array env x annotation a (st : source_state) gas =
    if st.frame.static_context then
      abrupt_result (InvalidCompletion "array push in static frame") st gas
    else case eval_atom st.scopes a of
      SOME (ReferenceValue
        (StorageReference PersistentStorage addr slot 0 (ArrayT element NONE) layout)) =>
        let old_length = w2n (lookup_storage slot
              (lookup_account addr st.world.accounts).storage) in
        if 2 ** 64 ≤ old_length then abrupt_result (PanicCompletion 65) st gas else
        (case fixed_array_element env addr (mapping_slot [] slot) element
                (old_length + 1) layout (&old_length) of
           ValueOk (ReferenceValue
             (StorageReference PersistentStorage _ data_slot offset _ _)) =>
             (case write_storage st.world.accounts addr slot 0 (UintT 256)
                     (IntegerValue (&(old_length + 1))) of
                SOME accounts =>
                  normal_result
                    (define_binding x annotation
                      (ReferenceValue (StorageReference PersistentStorage addr
                         data_slot offset element layout))
                      (scratch_write (SOME slot)
                        (st with world := st.world with accounts := accounts))) gas
              | NONE => abrupt_result (InvalidCompletion "bad array length write") st gas)
         | _ => abrupt_result (InvalidCompletion "bad array push element") st gas)
    | SOME (ReferenceValue
        (StorageReference PersistentStorage addr slot 0 BytesT layout)) =>
        (case push_storage_bytes st.world.accounts addr slot of
           INL (accounts, data_slot, offset) =>
             normal_result
               (define_binding x annotation
                 (ReferenceValue (StorageReference PersistentStorage addr
                    data_slot offset (FixedBytesT 1) layout))
                 (scratch_write
                   (case storage_byte_length st.world.accounts addr slot of
                      INL length => if 31 ≤ length then SOME slot else NONE
                    | INR _ => NONE)
                   (st with world := st.world with accounts := accounts))) gas
         | INR c => abrupt_result c st gas)
    | _ => abrupt_result (InvalidCompletion "bad dynamic array reference") st gas
End

Definition pop_storage_array_def:
  pop_storage_array n env x annotation a (st : source_state) gas =
    if st.frame.static_context then
      abrupt_result (InvalidCompletion "array pop in static frame") st gas
    else case eval_atom st.scopes a of
      SOME (ReferenceValue
        (StorageReference PersistentStorage addr slot 0 (ArrayT element NONE) layout)) =>
        let old_length = w2n (lookup_storage slot
              (lookup_account addr st.world.accounts).storage) in
        if old_length = 0 then abrupt_result (PanicCompletion 49) st gas else
        (case fixed_array_element env addr (mapping_slot [] slot) element
                 old_length layout (&(old_length - 1)) of
           ValueOk (ReferenceValue
             (StorageReference PersistentStorage _ data_slot offset _ _)) =>
             (case clear_storage_value env (n + LENGTH env.type_declarations)
                     st.world.accounts addr data_slot offset element of
                INL (accounts, scratch) =>
                  (case write_storage accounts addr slot 0 (UintT 256)
                          (IntegerValue (&(old_length - 1))) of
                     SOME accounts' =>
                       normal_result
                         (define_binding x annotation (TupleValue [])
                           (scratch_write (later_scratch (SOME slot) scratch)
                             (st with world := st.world with accounts := accounts'))) gas
                   | NONE => abrupt_result (InvalidCompletion "bad array length write") st gas)
              | INR c => abrupt_result c st gas)
         | _ => abrupt_result (InvalidCompletion "bad array pop element") st gas)
    | SOME (ReferenceValue
        (StorageReference PersistentStorage addr slot 0 BytesT layout)) =>
        (case pop_storage_bytes st.world.accounts addr slot of
           INL accounts =>
             normal_result
               (define_binding x annotation (TupleValue [])
                 (scratch_write (long_bytes_scratch st.world.accounts addr slot)
                   (st with world := st.world with accounts := accounts))) gas
         | INR c => abrupt_result c st gas)
    | _ => abrupt_result (InvalidCompletion "bad dynamic array reference") st gas
End

Definition eval_event_args_def:
  (eval_event_args scopes [] = SOME []) ∧
  (eval_event_args scopes ((ty, indexed, a) :: args) =
    case (eval_atom scopes a, eval_event_args scopes args) of
      (SOME v, SOME vs) => SOME ((ty, indexed, v) :: vs)
    | _ => NONE)
End

(* A log of the executing account, appended to the world's logs, so a revert
 * of the frame discards it with the rest of the world. As with storage
 * writes, an emit in a static frame fails. The compiler encodes the log's
 * data at the free memory pointer, which it does not move, reading the
 * pointer after the indexed arguments' hash preimages are written
 * (event_log). When reading an argument ends the frame, what the compiled
 * emit wrote by then stays in memory.
 *)
Definition emit_event_def:
  emit_event env topic args (st : source_state) gas =
    case eval_event_args st.scopes args of
      NONE => abrupt_result (InvalidCompletion "unbound atom") st gas
    | SOME vs =>
        case event_log env st st.frame.self_address topic vs of
          (INL (e, spill), st1) =>
            if st.frame.static_context then
              abrupt_result (InvalidCompletion "emit in static frame") st gas
            else
              let (p, st2) = memory_load 64 st1 in
              normal_result
                (memory_write (p + LENGTH e.data) spill
                   (memory_write p e.data st2) with
                   world := st2.world with logs := st2.world.logs ++ [e]) gas
        | (INR (c, ws), st1) =>
            abrupt_result c (apply_writes (FST (memory_load 64 st1)) ws st1) gas
End

(* The gas a call gives its callee with its gas option: the option, capped at
 * external_call_gas as the CALL opcode caps it at the gas left. *)
Definition callee_gas_def:
  (callee_gas scopes NONE = SOME external_call_gas) ∧
  (callee_gas scopes (SOME g) =
    case eval_atom scopes g of
      SOME (ScalarValue (IntegerValue n)) => SOME (MIN (Num n) external_call_gas)
    | _ => NONE)
End

(* Call and revert data as the compiler writes it at p: the selector as a
 * full word, then the encoded arguments after the selector's four bytes. *)
Definition write_call_data_def:
  write_call_data p selector data st =
    memory_write (p + LENGTH selector) data
      (if selector = [] then st
       else memory_write p (selector ++ REPLICATE 28 0w) st)
End

(* Where the compiler's revertWithError writes an error's selector and
 * encoded arguments: scratch 0 when the declared parameters are value types
 * whose encoding fits below 0x80 with the selector, the free memory pointer
 * otherwise, which it doesn't advance. *)
Definition error_payload_at_scratch_def:
  error_payload_at_scratch params ⇔
    EVERY is_value_type params ∧ 4 + 32 * LENGTH params ≤ 128
End

(* The compiler's revert_forward: the return data copied to the free memory
 * pointer, then reverted with. *)
Definition forward_revert_def:
  forward_revert data st = memory_write (FST (memory_load 64 st)) data st
End

(* A call's output region [p, p + size): the CALL opcode expands memory to
 * it and copies the first size bytes of the callee's return or revert data
 * there. *)
Definition call_output_def:
  call_output p size data st =
    memory_write p (TAKE size data) (memory_touch p size st)
End

(* The results a failed try call binds, never read: a memory result is the
 * zero slot. *)
Definition default_call_results_def:
  (default_call_results [] = SOME []) ∧
  (default_call_results (ty :: rets) =
    case ((case ty of
             LocatedT MemoryLoc element =>
               SOME (ReferenceValue (MemoryReference 96 element))
           | _ => OPTION_MAP ScalarValue (default_elementary ty)),
          default_call_results rets) of
      (SOME v, SOME vs) => SOME (v :: vs)
    | _ => NONE)
End

(* Constructor arguments use the same live-location ABI codec as calls. The
 * compiler copies the creation code to the free memory pointer, Panic(0x41)
 * when its end passes 2^64 - 1, encodes the arguments after it, and does not
 * move the pointer. A catching creation, as in try, binds the success flag,
 * the new address (zero on failure) and the revert data instead of
 * forwarding a failed creation's revert. *)
Definition call_create_def:
  call_create catching env x ty code params value salt args (st : source_state)
    gas =
    if st.frame.static_context then
      abrupt_result (InvalidCompletion "creation in static frame") st gas else
    case (eval_atom st.scopes value, eval_atoms st.scopes args,
          case salt of NONE => SOME NONE | SOME a =>
            case eval_atom st.scopes a of
              SOME (ScalarValue (BytesValue bs)) =>
                if LENGTH bs = 32 then SOME (SOME (word_of_bytes_be bs)) else NONE
            | _ => NONE) of
      (SOME (ScalarValue (IntegerValue v)), SOME vs, SOME salt) =>
        let (p, st0) = memory_load 64 st in
        if 2 ** 64 ≤ p + LENGTH code then abrupt_result (PanicCompletion 65) st gas else
        (case encoded_runtime_values env st0 params vs of
           (INR (c, ws), st1) =>
             abrupt_result c
               (if abi_read_failure c then
                  apply_writes (p + LENGTH code) ws (memory_write p code st1)
                else st) gas
         | (INL (data, spill), st1) =>
             let st2 = memory_write (p + LENGTH code + LENGTH data) spill
                         (memory_write p (code ++ data) st1) in
             case run_create_call st.frame.self_address salt (code ++ data)
                    (Num v) external_call_gas st2.world.accounts
                    st2.world.original st2.world.transient
                    st2.frame.tx_params of
               NONE => abrupt_result (InvalidCompletion "creation outside the model") st gas
             | SOME r =>
                 let st3 = st2 with <|
                   return_data := SOME r.create_return;
                   world := st2.world with <| accounts := r.create_accounts;
                               transient := r.create_transient;
                               logs := st2.world.logs ++ r.create_logs;
                               original := r.create_original;
                               to_delete := st2.world.to_delete ++ r.create_to_delete |> |> in
                 case r.create_address of
                   NONE =>
                     if catching then
                       normal_result (define_binding x ty
                         (TupleValue [ScalarValue (BoolValue F);
                                      ScalarValue (AddressValue 0w);
                                      ScalarValue (BytesValue r.create_return)])
                         st3) gas
                     else
                       abrupt_result (RevertCompletion r.create_return)
                         (forward_revert r.create_return st3) gas
                 | SOME addr => normal_result
                     (define_binding x ty
                       (if catching then
                          TupleValue [ScalarValue (BoolValue T);
                                      ScalarValue (AddressValue addr);
                                      ScalarValue (BytesValue [])]
                        else ScalarValue (AddressValue addr)) st3) gas)
    | _ => abrupt_result (InvalidCompletion "bad creation operands") st gas
End

(* A high-level call, as the compiler makes it: a call that expects no return
 * data reverts on a target without code; the selector word, then the encoded
 * arguments, at the free memory pointer p; the call's output region at p,
 * as long as the static return data, or empty when it is dynamic; a failed
 * call reverts with the callee's revert data. On success, dynamic return
 * data is copied to p; the free memory pointer moves past the return data,
 * at most the static size, Panic(0x41) past 2^64 - 1; the results are decoded
 * from it, a decoder rejection reverting with no data, and memory results are
 * copied after it. A successful call leaves the world the callee left, with
 * its logs after the caller's. Whatever the outcome, the callee's return or
 * revert bytes become the return data.
 *)
Definition call_external_mode_def:
  call_external_mode catching env x ty kind selector params rets target value
                g args (st : source_state) gas =
    case (eval_atom st.scopes target, eval_atom st.scopes value,
          callee_gas st.scopes g, eval_atoms st.scopes args) of
      (SOME (ScalarValue (AddressValue callee)),
       SOME (ScalarValue (IntegerValue v)), SOME limit, SOME vs) =>
        if rets = [] ∧ (lookup_account callee st.world.accounts).code = []
        then abrupt_result (RevertCompletion []) st gas
        else
        let (p, st0) = memory_load 64 st in
        (case encoded_runtime_values env st0 params vs of
           (INR (c, ws), st1) =>
             abrupt_result c
               (if abi_read_failure c then
                  apply_writes (p + LENGTH selector) ws (write_call_data p selector [] st1)
                else st) gas
         | (INL (data, spill), st1) =>
           let st2 = memory_write (p + LENGTH selector + LENGTH data) spill
                       (write_call_data p selector data st1) in
           let static = (kind = ExternalStaticCall ∨ st.frame.static_context) in
           if static ∧ v ≠ 0 then
             abrupt_result (InvalidCompletion "value in static frame") st gas
           else
             case (if kind = ExternalDelegateCall then
                     run_delegate_call st.frame.self_address st.frame.sender_address
                       st.frame.call_value callee (selector ++ data) static limit
                       st2.world.accounts st2.world.original
                       st2.world.transient st.frame.tx_params
                   else
                     run_external_call st.frame.self_address callee
                       (selector ++ data) (Num v) static limit
                       st2.world.accounts st2.world.original
                       st2.world.transient st.frame.tx_params) of
               NONE =>
                 abrupt_result (InvalidCompletion "call outside the model") st gas
             | SOME r =>
               let ret_types = abi_types env (LENGTH env.type_declarations) rets in
               let dynamic = EXISTS is_dynamic ret_types in
               let out = if dynamic then 0 else head_lengths ret_types 0 in
               let st3 = call_output p out r.call_return
                           (st2 with return_data := SOME r.call_return) in
               if ¬r.call_success then
                 if ¬catching then
                   abrupt_result (RevertCompletion r.call_return)
                     (forward_revert r.call_return st3) gas
                 else
                   (case default_call_results rets of
                      NONE => abrupt_result (InvalidCompletion "bad try return types") st3 gas
                    | SOME defaults =>
                        let values = ScalarValue (BoolValue F) :: defaults in
                        normal_result (define_binding x ty
                          (TupleValue (values ++
                            [ScalarValue (BytesValue r.call_return)])) st3) gas)
               else
                 let st4 = st3 with world :=
                       st3.world with <| accounts := r.call_accounts;
                          transient := r.call_transient;
                          logs := st3.world.logs ++ r.call_logs;
                          original := r.call_original;
                          to_delete := st3.world.to_delete ++ r.call_to_delete |> in
                 let size = if dynamic then LENGTH r.call_return
                            else MIN out (LENGTH r.call_return) in
                 let st5 = if dynamic then memory_write p r.call_return st4 else st4 in
                 case finalize_allocation p size st5 of
                   INR c => abrupt_result c st5 gas
                 | INL st6 =>
                 case decode_arguments env rets (FST (memory_read p size st6)) 0
                        (FST (memory_load 64 st6)) of
                   INL rvs =>
                     (case materialize_arguments env rets rvs st6 of
                        INL (values, st7) =>
                          let result = if catching then
                                TupleValue (ScalarValue (BoolValue T) :: values ++
                                  [ScalarValue (BytesValue [])])
                              else pack_results values in
                          normal_result (define_binding x ty result st7) gas
                      | INR c => abrupt_result c st6 gas)
                 | INR c => abrupt_result c st6 gas)
    | _ => abrupt_result (InvalidCompletion "bad call operands") st gas
End

Definition call_external_def:
  call_external env x ty kind selector params rets target value g args st gas =
    call_external_mode F env x ty kind selector params rets target value g args
      st gas
End

(* The compiler's extract_returndata: no return data is the zero slot; other
 * return data is copied to a new memory bytes, its padding left as it was. *)
Definition materialize_revert_data_def:
  materialize_revert_data data st =
    if data = [] then INL (ReferenceValue (MemoryReference 96 BytesT), st)
    else case allocate_byte_array (LENGTH data) st of
      INL (p, st1) =>
        INL (ReferenceValue (MemoryReference p BytesT), memory_write (p + 32) data st1)
    | INR c => INR c
End

(* The compiler's catch decoders. Both first copy the selector to the scratch
 * space when there is one. Panic copies its code word to the scratch space.
 * Error copies the data after the selector to the free memory pointer, where
 * the string stays: the decoder does not require canonical offsets or
 * padding, and only a successful decode moves the free memory pointer. *)
Definition try_decode_error_def:
  try_decode_error kind data st =
    let st0 = if 3 < LENGTH data then memory_write 0 (TAKE 4 data) st else st in
    case kind of
      PanicCatch =>
        if 36 ≤ LENGTH data ∧ TAKE 4 data = [0x4ew; 0x48w; 0x7bw; 0x71w] then
          INL (TupleValue [ScalarValue (BoolValue T);
                            ScalarValue (IntegerValue (&(abi_word data 4)))],
               memory_write 0 (TAKE 32 (DROP 4 data)) st0)
        else INL (TupleValue [ScalarValue (BoolValue F);
                            ScalarValue (IntegerValue 0)], st0)
    | ErrorCatch =>
        let missing = TupleValue [ScalarValue (BoolValue F);
              ReferenceValue (MemoryReference 96 StringT)] in
        if LENGTH data < 68 ∨ TAKE 4 data ≠ [0x08w; 0xc3w; 0x79w; 0xa0w] then
          INL (missing, st0) else
        let (p, st1) = memory_load 64 st0 in
        let st2 = memory_write p (DROP 4 data) st1 in
        let offset = abi_word data 4 in
        if 2 ** 64 ≤ offset ∨ offset + 36 > LENGTH data then INL (missing, st2) else
        let length = abi_word data (offset + 4) in
        if 2 ** 64 ≤ length ∨ offset + 36 + length > LENGTH data then
          INL (missing, st2) else
        (case finalize_allocation p (offset + 32 + length) st2 of
           INL st3 =>
             INL (TupleValue [ScalarValue (BoolValue T);
                    ReferenceValue (MemoryReference (p + offset) StringT)], st3)
         | INR c => INR c)
    | GenericCatch => INR (InvalidCompletion "generic catch decoder")
End

(* transfer requests gas only when value is zero: the EVM adds the stipend
 * for nonzero value. Returndata is forwarded on failure and never allocated. *)
Definition call_transfer_def:
  call_transfer x ty target value (st : source_state) gas =
    case (eval_atom st.scopes target, eval_atom st.scopes value) of
      (SOME (ScalarValue (AddressValue callee)),
       SOME (ScalarValue (IntegerValue v))) =>
        if st.frame.static_context ∧ v ≠ 0 then
          abrupt_result (InvalidCompletion "value in static frame") st gas
        else
          (case run_external_call st.frame.self_address callee [] (Num v)
                 st.frame.static_context (if v = 0 then call_stipend else 0)
                 st.world.accounts st.world.original
                 st.world.transient st.frame.tx_params of
            NONE => abrupt_result (InvalidCompletion "call outside the model") st gas
          | SOME res =>
              if ¬res.call_success then
                abrupt_result (RevertCompletion res.call_return)
                  (forward_revert res.call_return st) gas
              else
                let st' = st with
                  <| world := st.world with <| accounts := res.call_accounts;
                                 transient := res.call_transient;
                                 logs := st.world.logs ++ res.call_logs;
                                 original := res.call_original;
                                 to_delete := st.world.to_delete ++ res.call_to_delete |>;
                     return_data := SOME res.call_return |> in
                normal_result (define_binding x ty (TupleValue []) st') gas)
    | _ => abrupt_result (InvalidCompletion "bad transfer operands") st gas
End

(* A low-level target.call(data), target.staticcall(data) or
 * target.delegatecall(data), as the compiler makes it: memory data sent from
 * where it is, any other data packed at the free memory pointer first
 * (packed_call_data); no check that the target has code, no output region,
 * and a failure returned rather than reverted. A delegate call runs the
 * target's code in this contract's account, with this frame's sender and
 * value. The return data is materialized as extract_returndata does, and is
 * also the frame's return data from then on.
 *)
Definition call_low_level_def:
  call_low_level x ty kind target value g data (st : source_state) gas =
    case (eval_atom st.scopes target, eval_atom st.scopes value,
          callee_gas st.scopes g, eval_atom st.scopes data) of
      (SOME (ScalarValue (AddressValue callee)),
       SOME (ScalarValue (IntegerValue v)), SOME limit, SOME d) =>
        (case (case d of
                 ReferenceValue (MemoryReference q rty) =>
                   byte_contents st (MemoryReference q rty)
               | _ => packed_call_data st d) of
           INR c => abrupt_result c st gas
         | INL (bs, st0) =>
           let static = (kind = ExternalStaticCall ∨ st.frame.static_context) in
           if static ∧ v ≠ 0 then
             abrupt_result (InvalidCompletion "value in static frame") st gas
           else
           case (if kind = ExternalDelegateCall then
                   run_delegate_call st.frame.self_address st.frame.sender_address
                     st.frame.call_value callee bs static limit
                     st0.world.accounts st0.world.original
                     st0.world.transient st.frame.tx_params
                 else
                   run_external_call st.frame.self_address callee bs (Num v)
                     static limit st0.world.accounts
                     st0.world.original st0.world.transient
                     st.frame.tx_params) of
             NONE => abrupt_result (InvalidCompletion "call outside the model") st gas
           | SOME res =>
             let st1 = st0 with return_data := SOME res.call_return in
             let st2 = if res.call_success then
                   st1 with world :=
                     st1.world with <| accounts := res.call_accounts;
                        transient := res.call_transient;
                        logs := st1.world.logs ++ res.call_logs;
                        original := res.call_original;
                        to_delete := st1.world.to_delete ++ res.call_to_delete |>
                 else st1 in
             let success = ScalarValue (BoolValue res.call_success) in
             case materialize_revert_data res.call_return st2 of
               INL (v, st3) =>
                 normal_result (define_binding x ty (TupleValue [success; v]) st3) gas
             | INR c => abrupt_result c st2 gas)
    | _ => abrupt_result (InvalidCompletion "bad low-level call operands") st gas
End

(* The selector an ABI encoding starts with: none, or four bytes. *)
Definition selector_bytes_def:
  selector_bytes scopes selector =
    case selector of
      NONE => SOME []
    | SOME s =>
        case eval_atom scopes s of
          SOME (ScalarValue (BytesValue bs)) => if LENGTH bs = 4 then SOME bs else NONE
        | _ => NONE
End

(* An ABI encoding as a new memory bytes, or string (string.concat), as the
 * compiler makes it at the free memory pointer p: the selector word and the
 * encoding at p + 32, the length at p, then the free memory pointer moved
 * past them, Panic(0x41) past 2^64 - 1. *)
Definition allocate_encoding_def:
  allocate_encoding x ty prefix bs spill st gas =
    let (p, st1) = memory_load 64 st in
    let n = LENGTH prefix + LENGTH bs in
    case finalize_allocation p (32 + n)
           (memory_store p n (memory_write (p + 32 + n) spill
              (write_call_data (p + 32) prefix bs st1))) of
      INR c => abrupt_result c st gas
    | INL st2 =>
        let element = if ty = SingleType (LocatedT MemoryLoc StringT) then StringT
                      else BytesT in
        normal_result (define_binding x ty
          (ReferenceValue (MemoryReference p element)) st2) gas
End

Definition abi_encode_def:
  abi_encode env x ty selector tys args st gas =
    case (selector_bytes st.scopes selector, eval_atoms st.scopes args) of
      (SOME prefix, SOME vs) =>
        (case encoded_runtime_values env st tys vs of
           (INL (bs, spill), st1) => allocate_encoding x ty prefix bs spill st1 gas
         | (INR (c, ws), st1) =>
             let p = FST (memory_load 64 st1) in
             abrupt_result c
               (if abi_read_failure c then
                  apply_writes (p + 32 + LENGTH prefix) ws
                    (write_call_data (p + 32) prefix [] st1)
                else st) gas)
    | _ => abrupt_result (InvalidCompletion "bad abi.encode operands") st gas
End

Definition abi_encode_packed_def:
  abi_encode_packed env x ty tys args st gas =
    case eval_atoms st.scopes args of
      SOME vs =>
        (case packed_encoding env st tys vs of
           (INL (bs, spill), st1) => allocate_encoding x ty [] bs spill st1 gas
         | (INR (c, ws), st1) =>
             abrupt_result c (apply_writes (FST (memory_load 64 st1) + 32) ws st1) gas)
    | NONE => abrupt_result (InvalidCompletion "bad abi.encodePacked operands") st gas
End

(* Every statement except internal calls, if and while. *)
Definition simple_stmt_def:
  simple_stmt n env s st gas =
    case s of
      DefineStmt x ty (EnvironmentOperation GasLeft) =>
        (case gas of
           GasLeftObservation g :: rest =>
             if g < 2 ** 256 then
               normal_result (define_binding x ty (ScalarValue (IntegerValue (&g))) st) rest
             else abrupt_result (InvalidCompletion "missing gasleft observation") st gas
         | _ => abrupt_result (InvalidCompletion "missing gasleft observation") st gas)
    (* A literal is copied to a new byte sequence a full word at a time. *)
    | DefineStmt x ty (BytesLiteralOperation element bs) =>
        (case allocate_byte_array (LENGTH bs) st of
           INL (p, st1) =>
             normal_result (define_binding x ty
               (ReferenceValue (MemoryReference p element))
               (memory_write (p + 32)
                  (bs ++ REPLICATE ((LENGTH bs + 31) DIV 32 * 32 - LENGTH bs) 0w)
                  st1)) gas
         | INR c => abrupt_result c st gas)
    | DefineStmt x ty (DefaultMemoryOperation element) =>
        (case zero_value env (LENGTH env.type_declarations) element st of
           INL (p, st1) =>
             normal_result (define_binding x ty
               (ReferenceValue (MemoryReference p element)) st1) gas
         | INR c => abrupt_result c st gas)
    (* new T[](n) and new bytes(n) are zeroed; a struct constructor or array
     * literal's memory is allocated and then written by the statements after. *)
    | DefineStmt x ty (AllocateMemoryOperation element length) =>
        (case eval_atom st.scopes length of
           SOME (ScalarValue (IntegerValue n)) =>
             if n < 0 then abrupt_result (InvalidCompletion "negative allocation") st gas
             else
               (case (case element of
                        ArrayT _ (SOME k) =>
                          if Num n ≠ k then INR (InvalidCompletion "bad array allocation")
                          else allocate_memory (32 * k) st
                      | StructT s =>
                          (case lookup_struct env s of
                             SOME fields =>
                               if Num n ≠ LENGTH fields then
                                 INR (InvalidCompletion "bad struct allocation")
                               else allocate_memory (32 * Num n) st
                           | NONE => INR (InvalidCompletion "unknown struct"))
                      | _ => new_memory_array env element (Num n) st) of
                  INL (p, st1) =>
                    normal_result (define_binding x ty
                      (ReferenceValue (MemoryReference p element)) st1) gas
                | INR c => abrupt_result c st gas)
         | _ => abrupt_result (InvalidCompletion "bad allocation length") st gas)
    | DefineStmt x ty (CopyToMemoryOperation a) =>
        (case eval_atom st.scopes a of
           SOME (ReferenceValue (CalldataReference data n rty)) =>
             (case copy_calldata_array env st.frame.call_data rty data n
                     (FST (memory_load 64 st)) of
                INL v =>
                  (case materialize_value env rty v st of
                     INL (v', st') => normal_result (define_binding x ty v' st') gas
                   | INR c => abrupt_result c st gas)
              | INR c => abrupt_result c st gas)
         | SOME (ReferenceValue (StorageReference PersistentStorage addr slot 0 rty _)) =>
             (case materialize_storage env (LENGTH env.type_declarations)
                     st.world.accounts addr slot rty st of
                INL (v', st') => normal_result (define_binding x ty v' st') gas
              | INR (c, st') => abrupt_result c st' gas)
         | _ => abrupt_result (InvalidCompletion "bad object copy") st gas)
    (* Decoded memory values are allocated, as external call results are. A
     * memory input is decoded in place: only its bytes below the memory size
     * are read, the rest being zeros, as the compiler's decoder reads only
     * the words it needs from an input of any length, and its reads touch
     * memory up to the last of them. The compiled decoder allocates at the
     * free memory pointer as it reads, so a decode that reads there is left
     * unsupported, as is a failing one whose input reaches past the memory
     * size or the free memory pointer, since its failure does not say how
     * far it read. Its allocations rewrite the pointer's own word, so a
     * decode reading [64, 96) is unsupported too. The decoder compares the input's length with the heads'
     * as signed words, slt(sub(dataEnd, headStart), size), so a length word
     * of 2^255 or more reverts before anything is read. *)
    | DefineStmt x ty (AbiDecodeOperation tys a) =>
        (case eval_atom st.scopes a of
           SOME (ReferenceValue r) =>
             (case decode_source st r of
                INL (bs, input_len, st0) =>
                  if 2 ** 255 ≤ input_len then abrupt_result (RevertCompletion []) st0 gas else
                  let free = FST (memory_load 64 st0) in
                  let bound = decode_bound r free input_len in
                  (case decode_input env tys bs input_len bound 0 free of
                     INL (vs, reach) =>
                       if bound < reach then
                         abrupt_result (InvalidCompletion
                           "unsupported: abi.decode reading at the free memory pointer")
                           st gas
                       else if decode_reads_free_pointer r reach then
                         abrupt_result (InvalidCompletion
                           "unsupported: abi.decode input overlapping the free memory pointer")
                           st gas
                       else
                       (case materialize_arguments env tys vs (decode_reads r reach st0) of
                          INL (values, st1) =>
                            normal_result (define_binding x ty (pack_results values) st1) gas
                        | INR c => abrupt_result c st gas)
                   | INR c =>
                       if LENGTH bs < input_len ∨ bound < input_len then
                         abrupt_result (InvalidCompletion
                           "unsupported: abi.decode failing on an input past the memory size or the free memory pointer")
                           st gas
                       else if decode_reads_free_pointer r input_len then
                         abrupt_result (InvalidCompletion
                           "unsupported: abi.decode input overlapping the free memory pointer")
                           st gas
                       else abrupt_result c st0 gas)
              | INR c => abrupt_result c st gas)
         | _ => abrupt_result (InvalidCompletion "bad abi.decode operand") st gas)
    | DefineStmt x ty (AbiEncodeOperation selector tys args) =>
        abi_encode env x ty selector tys args st gas
    | DefineStmt x ty (AbiEncodePackedOperation tys args) =>
        abi_encode_packed env x ty tys args st gas
    | DefineStmt x ty (ArrayPushOperation a) =>
        push_storage_array env x ty a st gas
    | DefineStmt x ty (ArrayPopOperation a) =>
        pop_storage_array n env x ty a st gas
    | DefineStmt x ty (ExternalCallOperation kind selector params rets target
                         value g args) =>
        call_external env x ty kind selector params rets target value g args st gas
    | DefineStmt x ty (LowLevelCallOperation kind target value g data) =>
        call_low_level x ty kind target value g data st gas
    | DefineStmt x ty (CreateContractOperation code params value salt args) =>
        call_create F env x ty code params value salt args st gas
    | DefineStmt x ty (TryCreateContractOperation code params value salt args) =>
        call_create T env x ty code params value salt args st gas
    | DefineStmt x ty (TryDecodeErrorOperation kind a) =>
        (case eval_atom st.scopes a of
           SOME (ScalarValue (BytesValue data)) =>
             (case try_decode_error kind data st of
                INL (v, st1) => normal_result (define_binding x ty v st1) gas
              | INR c => abrupt_result c st gas)
         | _ => abrupt_result (InvalidCompletion "bad catch data") st gas)
    | DefineStmt x ty (MaterializeRevertDataOperation a) =>
        (case eval_atom st.scopes a of
           SOME (ScalarValue (BytesValue data)) =>
             (case materialize_revert_data data st of
                INL (v, st1) => normal_result (define_binding x ty v st1) gas
              | INR c => abrupt_result c st gas)
         | _ => abrupt_result (InvalidCompletion "bad catch data") st gas)
    | DefineStmt x ty (TransferOperation target value) =>
        call_transfer x ty target value st gas
    | DefineStmt x ty (TryExternalCallOperation kind selector params rets target
                         value g args) =>
        call_external_mode T env x ty kind selector params rets target value g
          args st gas
    (* Clear return data after precompile builtins that leave it unknown. *)
    | DefineStmt x ty (BuiltinOperation b args) =>
        (case eval_atoms st.scopes args of
           SOME vs =>
             (case eval_builtin st b vs of
                INL (v, st') =>
                  normal_result (define_binding x ty v
                    (if builtin_calls_precompile b then st' with return_data := NONE
                     else st')) gas
              | INR c => abrupt_result c st gas)
         | NONE => abrupt_result (InvalidCompletion "bad builtin operands") st gas)
    | DefineStmt x ty op =>
        (case eval_operation env st op of
           INL (v, st1) => normal_result (define_binding x ty v st1) gas
         | INR c => abrupt_result c st gas)
    | CaptureBindingStmt t x =>
        normal_result
          (st with targets := set_target t (BindTarget x) st.targets) gas
    | CaptureValueStmt t a =>
        (case eval_atom st.scopes a of
           SOME (ReferenceValue r) =>
             normal_result
               (st with targets := set_target t (ValueTarget r) st.targets) gas
         | _ => abrupt_result (InvalidCompletion "bad captured reference") st gas)
    | CaptureReferenceFieldStmt t a (FieldNavigation f) =>
        (case eval_atom st.scopes a of
           SOME (ReferenceValue (MemoryReference p (StructT s))) =>
             (case memory_struct_field env s p f of
                INL (q, fty) =>
                  normal_result (st with targets := set_target t
                    (ValueTarget (MemoryWordReference q fty)) st.targets) gas
              | INR c => abrupt_result c st gas)
         | _ => abrupt_result (InvalidCompletion "bad struct field capture") st gas)
    | CaptureReferenceFieldStmt t a (IndexNavigation index) =>
        (case (eval_atom st.scopes a, eval_atom st.scopes index) of
           (SOME (ReferenceValue (MemoryReference p rty)),
            SOME (ScalarValue (IntegerValue i))) =>
             if byte_sequence_type rty then
               (case memory_byte_element p i st of
                  INL (q, st1) =>
                    normal_result (st1 with targets := set_target t
                      (ValueTarget (MemoryReference q (FixedBytesT 1))) st1.targets) gas
                | INR c => abrupt_result c st gas)
             else
               (case memory_array_element rty p i st of
                  INL (q, element, st1) =>
                    normal_result (st1 with targets := set_target t
                      (ValueTarget (MemoryWordReference q element)) st1.targets) gas
                | INR c => abrupt_result c st gas)
         | _ => abrupt_result (InvalidCompletion "bad array element capture") st gas)
    | BindReferenceStmt t _ a =>
        (case write_target env t a st of
           SOME st' => normal_result st' gas
         | NONE => abrupt_result (InvalidCompletion "bad reference binding") st gas)
    | CopyContentsStmt src_ty _ a b =>
        (case (eval_atom st.scopes a, eval_atom st.scopes b) of
           (SOME (ReferenceValue src), SOME (ReferenceValue dst)) =>
             (case (case src_ty of
                      LocatedT _ (ArrayT element length) => SOME (ArrayT element length)
                    | LocatedT _ (StructT s) => SOME (StructT s)
                    | _ => NONE) of
                SOME cty =>
                  (* The compiler's storage-to-storage copy returns at once
                   * when the source is the destination. *)
                  if (case (src, dst) of
                        (StorageReference PersistentStorage src_addr src_slot 0 _ _,
                         StorageReference PersistentStorage dst_addr dst_slot 0 _ _) =>
                          src_addr = dst_addr ∧ src_slot = dst_slot
                      | _ => F)
                  then normal_result st gas else
                  if st.frame.static_context then
                    abrupt_result (InvalidCompletion "array copy in static frame") st gas
                  else
                  (* A memory source is read as the copy reaches it. *)
                  (case (case src of
                           MemoryReference _ _ => (INL (ReferenceValue src), st)
                         | _ =>
                             (case array_copy_value env 0 st cty src of
                                (INL v, _, st1) => (INL v, st1)
                              | (INR (c, _), _, st1) => (INR c, st1))) of
                     (INL v, st1) =>
                       (case copy_to_storage env cty v dst st.frame.static_context st1 of
                          (INL _, st2) => normal_result st2 gas
                        | (INR c, st2) => abrupt_result c st2 gas)
                   | (INR c, st1) => abrupt_result c st1 gas)
              | NONE =>
                case copy_byte_contents src dst st of
                  (INL _, st1) => normal_result st1 gas
                | (INR c, st1) => abrupt_result c st1 gas)
         | _ => abrupt_result (InvalidCompletion "bad byte sequence copy") st gas)
    | ResetTargetStmt t ty => reset_target n env t ty st gas
    | WriteScalarStmt t ty a =>
        (case write_target env t a st of
           SOME st' => normal_result st' gas
         | NONE => abrupt_result (InvalidCompletion "bad scalar write") st gas)
    | ReturnStmt atoms =>
        (case eval_atoms st.scopes atoms of
           SOME vs => abrupt_result (ReturnCompletion vs) st gas
         | NONE =>
             abrupt_result
               (InvalidCompletion "unbound atom") st gas)
    | BreakStmt => abrupt_result BreakCompletion st gas
    | ContinueStmt => abrupt_result ContinueCompletion st gas
    | PanicStmt code => abrupt_result (PanicCompletion code) st gas
    | EmitStmt topic args => emit_event env topic args st gas
    | RevertErrorStmt selector params args =>
        (case eval_atoms st.scopes args of
           SOME vs =>
             (case encoded_runtime_values env st params vs of
                (r, st1) =>
                  let (p, st2) = if error_payload_at_scratch params then (0, st1)
                                 else memory_load 64 st1 in
                  case r of
                    INL (data, spill) =>
                      abrupt_result (RevertCompletion (selector ++ data))
                        (memory_write (p + LENGTH selector + LENGTH data) spill
                          (write_call_data p selector data st2)) gas
                  | INR (c, ws) =>
                      abrupt_result c
                        (if abi_read_failure c then
                           apply_writes (p + LENGTH selector) ws
                             (write_call_data p selector [] st2)
                         else st) gas)
         | NONE =>
             abrupt_result
               (InvalidCompletion "unbound atom") st gas)
    | RevertStmt a =>
        (case eval_atom st.scopes a of
           SOME (ScalarValue (BytesValue data)) =>
             abrupt_result (RevertCompletion data) (forward_revert data st) gas
         | _ => abrupt_result (InvalidCompletion "bad revert payload") st gas)
    | _ => abrupt_result (InvalidCompletion "unsupported statement") st gas
End

(* Inline assembly. A block runs in the Yul evaluator on a machine built from
 * the source state: the world, the frame, the frame's memory and a scope
 * binding each referenced declaration's Yul name to its word: a memory
 * variable's word is its address. The block reads and writes the memory the
 * source runs on, with Yul's semantics. On normal exit the referenced locals
 * and memory variables are written back: a value-type local's word must be
 * one the compiler could keep for its type, a memory variable takes the
 * address the block left. In a static frame, a block that names a builtin
 * changing the world (call included) fails closed, whether or not it would
 * run it.
 *
 * A call and staticcall run the callee as the source's own calls do
 * (run_external_call), with the machine's gas budget the one every call from
 * the source gets: a bare gas() as a call's gas argument stands for it, so
 * the budget is never a value the block sees; a gas() anywhere else reads
 * one gas observation. The return data
 * buffer starts as the source's return data. Where the source does not know
 * it, the buffer starts empty and a block that could read it before a call of
 * its own (assembly_calls_ok) fails closed.
 *)

(* The value of type ty a word written to a local stands for, with memory's
 * word cleanup; an enum word outside its members stands for none. *)
Definition assembly_value_def:
  assembly_value env ty (w : num) =
    case word_value env ty w of
      INL (ScalarValue s) => SOME s
    | _ => NONE
End

Definition assembly_reference_word_def:
  assembly_reference_word env (st : source_state) r =
    case r of
      AssemblyLocal x ty =>
        (case lookup_binding x st.scopes of
           SOME b =>
             (case b.binding_value of
                ScalarValue s => scalar_word env ty s
              | _ => NONE)
         | NONE => NONE)
    | AssemblySlot x =>
        OPTION_MAP (λv. w2n v.state_slot) (lookup_state_variable env x)
    | AssemblyOffset x =>
        OPTION_MAP (λv. v.state_offset) (lookup_state_variable env x)
    | AssemblyPointerSlot x =>
        (case lookup_binding x st.scopes of
           SOME b =>
             (case b.binding_value of
                ReferenceValue (StorageReference PersistentStorage _ slot _ _ _) =>
                  SOME (w2n slot)
              | _ => NONE)
         | NONE => NONE)
    | AssemblyPointerOffset x =>
        (case lookup_binding x st.scopes of
           SOME b =>
             (case b.binding_value of
                ReferenceValue (StorageReference PersistentStorage _ _ offset _ _) =>
                  SOME offset
              | _ => NONE)
         | NONE => NONE)
    | AssemblyCalldataOffset x =>
        (case lookup_binding x st.scopes of
           SOME b =>
             (case b.binding_value of
                ReferenceValue (CalldataReference offset _ _) => SOME offset
              | _ => NONE)
         | NONE => NONE)
    | AssemblyCalldataLength x =>
        (case lookup_binding x st.scopes of
           SOME b =>
             (case b.binding_value of
                ReferenceValue (CalldataReference _ length _) => SOME length
              | _ => NONE)
         | NONE => NONE)
    | AssemblyConstant a ty =>
        (case eval_atom st.scopes a of
           SOME (ScalarValue s) => scalar_word env ty s
         | _ => NONE)
    | AssemblyMemory x _ =>
        (case lookup_binding x st.scopes of
           SOME b =>
             (case b.binding_value of
                ReferenceValue (MemoryReference p _) => SOME p
              | _ => NONE)
         | NONE => NONE)
End

(* The words of a block's references: the assignable ones' (locals, storage
 * pointer slots, memory variables and calldata references) as the block's
 * initial scope, and the read-only ones' by name, for the code to hold as
 * literals. *)
Definition assembly_inputs_def:
  (assembly_inputs env st [] =
    SOME (FEMPTY : string |-> bytes32, [] : (string # bytes32) list)) ∧
  (assembly_inputs env st ((name, r) :: refs) =
    case (assembly_reference_word env st r, assembly_inputs env st refs) of
      (SOME w, SOME (scope, literals)) =>
        (case r of
           AssemblyLocal _ _ => SOME (scope |+ (name, n2w w), literals)
         | AssemblyPointerSlot _ => SOME (scope |+ (name, n2w w), literals)
         | AssemblyMemory _ _ => SOME (scope |+ (name, n2w w), literals)
         | AssemblyCalldataOffset _ => SOME (scope |+ (name, n2w w), literals)
         | AssemblyCalldataLength _ => SOME (scope |+ (name, n2w w), literals)
         | _ => SOME (scope, (name, n2w w) :: literals))
    | _ => NONE)
End

(* The code with each name in sub read as its word, as the compiler puts the
 * values of x.slot, x.offset and constants in the code. A Yul function's
 * parameters and results may reuse a name for its body; a let may not.
 * Nested function definitions aren't imported, so a body's narrowed sub never
 * reaches an inner function, where the compiler would see the block's names. *)
Definition yul_substitute_expr_def:
  (yul_substitute_expr sub (YulLit l) = YulLit l) ∧
  (yul_substitute_expr sub (YulName x) =
    case ALOOKUP sub x of
      SOME w => YulLit (LitNumber w)
    | NONE => YulName x) ∧
  (yul_substitute_expr sub (YulBuiltin b es) =
    YulBuiltin b (yul_substitute_exprs sub es)) ∧
  (yul_substitute_expr sub (YulApply f es) =
    YulApply f (yul_substitute_exprs sub es)) ∧
  (yul_substitute_exprs sub [] = []) ∧
  (yul_substitute_exprs sub (e :: es) =
    yul_substitute_expr sub e :: yul_substitute_exprs sub es)
End

(* sub without the names in xs. *)
Definition yul_unbind_def:
  (yul_unbind xs [] = ([] : (string # bytes32) list)) ∧
  (yul_unbind xs ((x, w) :: sub) =
    if MEM x xs then yul_unbind xs sub else (x, w) :: yul_unbind xs sub)
End

Definition yul_substitute_stmt_def:
  (yul_substitute_stmt sub (YulBlock ss) = YulBlock (yul_substitute_stmts sub ss)) ∧
  (yul_substitute_stmt sub (YulFunction f params results body) =
    YulFunction f params results
      (yul_substitute_stmts (yul_unbind (params ++ results) sub) body)) ∧
  (yul_substitute_stmt sub (YulLet xs NONE) = YulLet xs NONE) ∧
  (yul_substitute_stmt sub (YulLet xs (SOME e)) =
    YulLet xs (SOME (yul_substitute_expr sub e))) ∧
  (yul_substitute_stmt sub (YulAssign xs e) =
    YulAssign xs (yul_substitute_expr sub e)) ∧
  (yul_substitute_stmt sub (YulIf e body) =
    YulIf (yul_substitute_expr sub e) (yul_substitute_stmts sub body)) ∧
  (yul_substitute_stmt sub (YulSwitch e cases default) =
    YulSwitch (yul_substitute_expr sub e) (yul_substitute_cases sub cases)
      (yul_substitute_stmts sub default)) ∧
  (yul_substitute_stmt sub (YulFor pre c post body) =
    YulFor (yul_substitute_stmts sub pre) (yul_substitute_expr sub c)
      (yul_substitute_stmts sub post) (yul_substitute_stmts sub body)) ∧
  (yul_substitute_stmt sub YulBreak = YulBreak) ∧
  (yul_substitute_stmt sub YulContinue = YulContinue) ∧
  (yul_substitute_stmt sub YulLeave = YulLeave) ∧
  (yul_substitute_stmt sub (YulExprStmt e) =
    YulExprStmt (yul_substitute_expr sub e)) ∧
  (yul_substitute_stmts sub [] = []) ∧
  (yul_substitute_stmts sub (s :: ss) =
    yul_substitute_stmt sub s :: yul_substitute_stmts sub ss) ∧
  (yul_substitute_cases sub [] = []) ∧
  (yul_substitute_cases sub ((l, body) :: cases) =
    (l, yul_substitute_stmts sub body) :: yul_substitute_cases sub cases)
End

Definition assembly_machine_def:
  assembly_machine (st : source_state) scope =
    <| accounts := st.world.accounts; transient := st.world.transient;
       logs := st.world.logs; self_address := st.frame.self_address;
       caller_address := st.frame.sender_address;
       call_value := n2w st.frame.call_value;
       call_data := st.frame.call_data;
       return_data := (case st.return_data of NONE => [] | SOME bs => bs);
       code := (lookup_account st.frame.code_address st.world.accounts).code;
       objects := FEMPTY; immutable_offsets := FEMPTY;
       immutables := FEMPTY; memory := st.memory; memory_size := st.memory_size;
       gas_limit := external_call_gas; gas_observations := []; scopes := [scope];
       transaction_parameters := st.frame.tx_params;
       original := st.world.original; to_delete := st.world.to_delete |>
End

Definition assembly_world_def:
  assembly_world (m : yul_machine) =
    (<| accounts := m.accounts; transient := m.transient; logs := m.logs;
        original := m.original; to_delete := m.to_delete |> : source_world)
End

(* Writes a referenced local back from the block's final scopes; a location
 * or constant reference has nothing to write. A value-type local must hold a
 * word the compiler could keep for its type: a narrower one's other bits
 * clear (or its sign extended), an enum's a member. A memory variable is
 * rebound to the address the block left, keeping its type. A storage pointer
 * whose slot the block may have assigned is rebound to that slot of the
 * executing account, at offset 0, keeping its type, as the compiler keeps the
 * pointer as the slot alone. A calldata reference is rebound to the offset
 * and length the block leaves, keeping its type. *)
Definition assembly_write_one_def:
  assembly_write_one env self (name, r) scopes
                     (yscopes : (string |-> bytes32) list) =
    case r of
      AssemblyLocal x ty =>
        (case yul_lookup name yscopes of
           NONE => NONE
         | SOME w =>
             case assembly_value env ty (w2n w) of
               NONE => NONE
             | SOME s =>
                 if scalar_word env ty s = SOME (w2n w) then
                   update_binding x (ScalarValue s) scopes
                 else NONE)
    | AssemblyMemory x ty =>
        (case yul_lookup name yscopes of
           SOME w => update_binding x (ReferenceValue (MemoryReference (w2n w) ty)) scopes
         | NONE => NONE)
    | AssemblyPointerSlot x =>
        (case (yul_lookup name yscopes, lookup_binding x scopes) of
           (SOME w, SOME b) =>
             (case b.binding_value of
                ReferenceValue (StorageReference PersistentStorage _ _ _ ty layout) =>
                  update_binding x
                    (ReferenceValue
                       (StorageReference PersistentStorage self w 0 ty layout))
                    scopes
              | _ => NONE)
         | _ => NONE)
    | AssemblyCalldataOffset x =>
        (case (yul_lookup name yscopes, lookup_binding x scopes) of
           (SOME w, SOME b) =>
             (case b.binding_value of
                ReferenceValue (CalldataReference _ length ty) =>
                  update_binding x
                    (ReferenceValue (CalldataReference (w2n w) length ty)) scopes
              | _ => NONE)
         | _ => NONE)
    | AssemblyCalldataLength x =>
        (case (yul_lookup name yscopes, lookup_binding x scopes) of
           (SOME w, SOME b) =>
             (case b.binding_value of
                ReferenceValue (CalldataReference offset _ ty) =>
                  if calldata_slice_type ty then
                    update_binding x
                      (ReferenceValue (CalldataReference offset (w2n w) ty)) scopes
                  else NONE
              | _ => NONE)
         | _ => NONE)
    | _ => SOME scopes
End

(* The calldata bytes a calldata reference of type ty and length n covers,
 * as the compiler's accessors read them: a dynamic array's elements, a
 * fixed array's or struct's heads, a byte sequence's bytes. *)
Definition calldata_span_def:
  calldata_span env ty n =
    case ty of
      ArrayT element NONE => n * abi_stride env element
    | ArrayT _ (SOME _) => abi_head_size (abi_type env (LENGTH env.type_declarations) ty)
    | StructT _ => abi_head_size (abi_type env (LENGTH env.type_declarations) ty)
    | _ => n
End

(* A calldata local's reference lies inside the calldata. *)
Definition calldata_in_bounds_def:
  calldata_in_bounds env cd scopes x ⇔
    case lookup_binding x scopes of
      SOME b =>
        (case b.binding_value of
           ReferenceValue (CalldataReference offset n ty) =>
             offset + calldata_span env ty n ≤ LENGTH (cd : byte list)
         | _ => F)
    | NONE => F
End

(* Each calldata reference a block names still lies inside the calldata on
 * exit; one it rebound past the end fails closed. *)
Definition assembly_calldata_ok_def:
  (assembly_calldata_ok env cd scopes [] ⇔ T) ∧
  (assembly_calldata_ok env cd scopes ((_, r) :: refs) ⇔
    (case r of
       AssemblyCalldataOffset x => calldata_in_bounds env cd scopes x
     | AssemblyCalldataLength x => calldata_in_bounds env cd scopes x
     | _ => T) ∧
    assembly_calldata_ok env cd scopes refs)
End

Definition assembly_write_back_def:
  (assembly_write_back env self [] scopes yscopes = SOME scopes) ∧
  (assembly_write_back env self (r :: refs) scopes yscopes =
    case assembly_write_one env self r scopes yscopes of
      NONE => NONE
    | SOME scopes' => assembly_write_back env self refs scopes' yscopes)
End

(* The return data after a block that exits normally. A non-empty buffer
 * shows a call of the block ran; an empty one may also be the start's empty
 * buffer standing for return data the source does not know, which stays
 * unknown. *)
Definition assembly_return_data_def:
  assembly_return_data (st : source_state) (m : yul_machine) =
    if st.return_data = NONE ∧ m.return_data = [] then NONE
    else SOME m.return_data
End

(* The frame after an inline assembly block. A halting block leaves the
 * frame its memory, as the halt does in the compiled code. *)
Definition assembly_result_def:
  assembly_result env refs (st : source_state) (r : yul_result) gas =
    let gas = r.machine.gas_observations in
    let world = assembly_world r.machine in
    case r.completion of
      YulNormal =>
        (case assembly_write_back env st.frame.self_address refs st.scopes
                r.machine.scopes of
           SOME scopes =>
             if ¬assembly_calldata_ok env st.frame.call_data scopes refs then
               abrupt_result
                 (InvalidCompletion "assembly left a calldata reference outside the calldata")
                 st gas
             else
               normal_result (st with <| scopes := scopes; world := world;
                   memory := r.machine.memory;
                   memory_size := r.machine.memory_size;
                   return_data := assembly_return_data st r.machine |>) gas
         | NONE =>
             abrupt_result (InvalidCompletion "assembly write-back failed") st gas)
    | YulReturn data =>
        abrupt_result (HaltCompletion data)
          (st with <| world := world; memory := r.machine.memory;
                      memory_size := r.machine.memory_size |>) gas
    | YulRevert data =>
        abrupt_result (RevertCompletion data)
          (st with <| memory := r.machine.memory;
                      memory_size := r.machine.memory_size |>) gas
    | YulAbort => abrupt_result AbortCompletion st gas
    | YulInvalid reason => abrupt_result (InvalidCompletion reason) st gas
    | YulOutOfFuel => abrupt_result FuelExhausted st gas
    | _ =>
        abrupt_result (InvalidCompletion "assembly control escaped its block")
          st gas
End

Definition eval_assembly_def:
  eval_assembly n env code refs (st : source_state) gas =
    let code_bad =
          if (lookup_account st.frame.code_address st.world.accounts).code = []
          then [YCodeSize; YCodeCopy] else [];
        bad = if st.frame.static_context
              then assembly_unsupported ++ assembly_state_writes ++ code_bad
              else assembly_unsupported ++ code_bad in
    if ¬assembly_stmts_ok bad code then
      abrupt_result (InvalidCompletion "unsupported assembly builtin") st gas
    else if st.return_data = NONE ∧ ¬assembly_calls_ok code then
      abrupt_result (InvalidCompletion "assembly reads return data the source does not know") st gas
    else
    case assembly_inputs env st refs of
      NONE => abrupt_result (InvalidCompletion "bad assembly reference") st gas
    | SOME (scope, literals) =>
        assembly_result env refs st
          (run_yul n (yul_substitute_stmts literals code)
             (assembly_machine st scope with gas_observations := gas)) gas
End

(* Pieces of the recursive cases *)

Definition branch_of_def:
  branch_of (st : source_state) c =
    case eval_atom st.scopes c of
      SOME (ScalarValue (BoolValue b)) => SOME b
    | _ => NONE
End

(* A call's returned values, packed per call_result_type, bound to x. *)
Definition bind_call_result_def:
  bind_call_result x ty (r : source_result) =
    case r.completion of
      ReturnCompletion vs =>
        normal_result (define_binding x ty (pack_results vs) r.state)
          r.unused_gas_evidence
    | _ => r
End

Datatype:
  loop_step = LoopExit | LoopNext | LoopStop
End

(* After a loop body: break leaves the loop normally, normal completion and
 * continue go round again, anything else propagates.
 *)
Definition loop_after_body_def:
  loop_after_body c =
    case c of
      BreakCompletion => LoopExit
    | NormalCompletion => LoopNext
    | ContinueCompletion => LoopNext
    | _ => LoopStop
End

Definition enter_procedure_def:
  enter_procedure (st : source_state) scope =
    st with <| scopes := [scope]; targets := FEMPTY |>
End

Definition restore_caller_def:
  restore_caller (caller : source_state) (callee : source_state) =
    callee with <| scopes := caller.scopes; targets := caller.targets |>
End

(* A body's completion as the call's: falling through returns the current
 * return bindings, and break/continue cannot escape a procedure.
 *)
Definition procedure_completion_def:
  procedure_completion (p : core_procedure) (r : source_result) =
    case r.completion of
      NormalCompletion =>
        (case read_returns r.state.scopes p.return_bindings of
           SOME vs => ReturnCompletion vs
         | NONE => InvalidCompletion "missing return binding")
    | BreakCompletion => InvalidCompletion "break escaped procedure"
    | ContinueCompletion => InvalidCompletion "continue escaped procedure"
    | c => c
End

(* The evaluator *)

Definition eval_block_def:
  (eval_block (n : num) env [] st gas = normal_result st gas) ∧
  (eval_block n env (s :: ss) st gas =
    let r = eval_stmt n env s st gas in
    if r.completion = NormalCompletion
    then eval_block n env ss r.state r.unused_gas_evidence
    else r) ∧
  (eval_stmt n env (DefineStmt x ty (InternalCallOperation f atoms)) st gas =
    case eval_atoms st.scopes atoms of
      SOME args => bind_call_result x ty (invoke_source n env f args st gas)
    | NONE =>
        abrupt_result
          (InvalidCompletion "unbound atom") st gas) ∧
  (* A function value no function has, the zero value included, panics after
   * the arguments are evaluated, as the compiler's internal dispatch does.
   * So does, during creation, a function outside the creation code's
   * internal dispatch, which holds only the functions creation code names
   * as values. *)
  (eval_stmt n env (DefineStmt x ty (FunctionValueCallOperation g atoms)) st gas =
    case (eval_atom st.scopes g, eval_atoms st.scopes atoms) of
      (SOME (ScalarValue (InternalFunctionValue (INL f))), SOME args) =>
        if IS_NONE st.immutables ∧ ¬MEM f env.creation_function_ids then
          abrupt_result (PanicCompletion panic_zero_function) st gas
        else bind_call_result x ty (invoke_source n env f args st gas)
    | (SOME (ScalarValue (InternalFunctionValue (INR _))), SOME _) =>
        abrupt_result (PanicCompletion panic_zero_function) st gas
    | _ => abrupt_result (InvalidCompletion "bad function value call") st gas) ∧
  (eval_stmt n env (IfStmt c ts es) st gas =
    case branch_of st c of
      SOME T => pop_result (eval_block n env ts (push_scope st) gas)
    | SOME F => pop_result (eval_block n env es (push_scope st) gas)
    | NONE =>
        abrupt_result (InvalidCompletion "non-boolean condition") st gas) ∧
  (eval_stmt n env (WhileStmt prelude c body) st gas =
    eval_loop n env prelude c body st gas) ∧
  (eval_stmt n env (AssemblyStmt code refs) st gas =
    eval_assembly n env code refs st gas) ∧
  (eval_stmt n env s st gas = simple_stmt n env s st gas) ∧
  (* One iteration in a pushed scope; fuel is spent on the back edge. *)
  (eval_loop n env prelude c body st gas =
    let r1 = eval_block n env prelude (push_scope st) gas in
    if r1.completion ≠ NormalCompletion then pop_result r1 else
    case branch_of r1.state c of
      NONE =>
        pop_result
          (r1 with completion := InvalidCompletion "non-boolean condition")
    | SOME b =>
        if ¬b then pop_result r1 else
        let r2 = pop_result (eval_block n env body r1.state
                               r1.unused_gas_evidence) in
        case loop_after_body r2.completion of
          LoopExit => r2 with completion := NormalCompletion
        | LoopStop => r2
        | LoopNext =>
            if n = 0 then r2 with completion := FuelExhausted
            else eval_loop (n - 1) env prelude c body r2.state
                   r2.unused_gas_evidence) ∧
  (* A successful call completes with ReturnCompletion of the returned values,
   * whether the body returned explicitly or fell through.
   *)
  (invoke_source n env f args st gas =
    if n = 0 then abrupt_result FuelExhausted st gas else
    case lookup_procedure env f of
      NONE => abrupt_result (InvalidCompletion "unknown procedure") st gas
    | SOME p =>
        case entry_scope env p args of
          NONE => abrupt_result (InvalidCompletion "bad arguments") st gas
        | SOME scope =>
            let r = eval_block (n - 1) env p.body (enter_procedure st scope)
                      gas in
            abrupt_result (procedure_completion p r)
              (restore_caller st r.state) r.unused_gas_evidence)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<)
    (λx. case x of
           INL (n, env, ss, st, gas) => (n, list_size core_stmt_size ss)
         | INR (INL (n, env, s, st, gas)) => (n, core_stmt_size s)
         | INR (INR (INL (n, env, pre, c, bd, st, gas))) =>
             (n, list_size core_stmt_size pre +
                 list_size core_stmt_size bd + 1)
         | INR (INR (INR (n, env, f, args, st, gas))) => (n, 0))’ >>
  rw[solidityCoreTheory.core_stmt_size_def, listTheory.list_size_def] >>
  rename1 ‘core_atom_size a’ >> Cases_on ‘a’ >>
  simp[solidityCoreTheory.core_atom_size_def]
End

(* cv translation, so core programs run under cv_compute. Termination of the
 * translated evaluator follows a scaled (fuel, size) order on the cv encodings,
 * strictly decreasing on every cv input.
 *)

val () = cv_auto_trans abi_encode_def;
val () = cv_auto_trans abi_encode_packed_def;
val () = cv_auto_trans write_target_value_def;
val () = cv_auto_trans write_target_def;
val () = cv_auto_trans reset_target_def;
val () = cv_auto_trans simple_stmt_def;
val () = cv_auto_trans assembly_value_def;
val () = cv_auto_trans assembly_reference_word_def;
val () = cv_auto_trans assembly_inputs_def;
val yul_substitute_expr_pre_def = cv_auto_trans_pre
  "yul_substitute_expr_pre yul_substitute_exprs_pre" yul_substitute_expr_def;

Theorem yul_substitute_exprs_pre_all[local]:
  ∀es sub. EVERY (yul_substitute_expr_pre sub) es ⇒
    yul_substitute_exprs_pre sub es
Proof
  Induct >> simp[Once (cj 2 yul_substitute_expr_pre_def)]
QED

Theorem yul_substitute_expr_pre[cv_pre,local]:
  (∀e sub. yul_substitute_expr_pre sub e) ∧
  (∀es sub. yul_substitute_exprs_pre sub es)
Proof
  conj_asm1_tac >-
    (ho_match_mp_tac yulASTTheory.yul_expr_induction >> rpt strip_tac >>
     simp[Once (cj 1 yul_substitute_expr_pre_def)] >>
     rpt conj_tac >> rpt gen_tac >> rpt strip_tac >> gvs[] >>
     irule yul_substitute_exprs_pre_all >> fs[listTheory.EVERY_MEM]) >>
  rpt gen_tac >> irule yul_substitute_exprs_pre_all >> simp[listTheory.EVERY_MEM]
QED

val () = cv_auto_trans yul_unbind_def;
val () = cv_auto_trans yul_substitute_stmt_def;
val () = cv_auto_trans assembly_machine_def;
val () = cv_auto_trans assembly_world_def;
val () = cv_auto_trans assembly_write_one_def;
val () = cv_auto_trans calldata_span_def;
val () = cv_auto_trans calldata_in_bounds_def;
val () = cv_auto_trans assembly_calldata_ok_def;
val () = cv_auto_trans assembly_write_back_def;
val () = cv_auto_trans assembly_result_def;
val () = cv_auto_trans eval_assembly_def;
val () = cv_auto_trans bind_call_result_def;
val () = cv_auto_trans procedure_completion_def;

val () = cv_auto_trans_rec eval_block_def (
  WF_REL_TAC ‘inv_image ($< LEX $<)
    (λx. case x of
           INL (n, env, ss, st, gas) => (cv$c2n n, 2 * cv_size ss)
         | INR (INL (n, env, s, st, gas)) => (cv$c2n n, 2 * cv_size s + 1)
         | INR (INR (INL (n, env, pre, c, bd, st, gas))) =>
             (cv$c2n n, 2 * (cv_size pre + cv_size bd) + 1)
         | INR (INR (INR (n, env, f, args, st, gas))) => (cv$c2n n, 0))’ >>
  cv_termination_tac >>
  (* a while statement's prelude and body against its encoding *)
  rename1 ‘cv_snd (cv_snd x)’ >> Cases_on ‘x’ >> gvs[] >>
  rename1 ‘cv_snd y’ >> Cases_on ‘y’ >> gvs[]
);
