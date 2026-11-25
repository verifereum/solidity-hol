(* Dispatch, call prologue and elementary ABI properties. *)
Theory solidityEntryProps
Ancestors
  solidityEntry solidityABI solidityCoreWf solidityMemory solidityScalar
  yulEvaluator vfmConstants contractABI arithmetic list byte words
Libs
  wordsLib

Theorem dispatch_selector_hit:
  4 ≤ LENGTH fr.call_data ∧
  lookup_external (TAKE 4 fr.call_data) prog.external_functions = SOME e ∧
  (e.payable ∨ fr.call_value = 0) ∧
  lookup_procedure env e.external_procedure = SOME p ∧
  decode_arguments env (MAP SND p.parameters) (DROP 4 fr.call_data) 4 128 =
    INL args ⇒
  dispatch env prog fr = DispatchCall p args CallEntry
Proof
  rw[dispatch_def] >> fs[]
QED

Theorem call_contract_dispatch_call:
  dispatch (core_program_environment prog) prog fr = DispatchCall p args kind ⇒
  call_contract fuel prog imm fr w =
  run_entry fuel (core_program_environment prog) p args fr w (SOME imm) 0 NONE kind
Proof
  simp[call_contract_def, call_contract_with_gas_thm, run_entry_def]
QED

(* The frame form exposes the final memory image as well as the source result. *)
Theorem call_contract_dispatch_call_frame:
  dispatch (core_program_environment prog) prog fr = DispatchCall p args kind ⇒
  call_contract_frame fuel prog imm fr w gas =
    (FST (run_entry_frame fuel (core_program_environment prog) p args fr w
      (SOME imm) 0 NONE kind gas),
     SOME (SND (run_entry_frame fuel (core_program_environment prog) p args fr w
      (SOME imm) 0 NONE kind gas)) )
Proof
  simp[call_contract_frame_def, pairTheory.UNCURRY]
QED

(* Return encoding with the procedure record reduced to its return types. *)
Definition entry_output_types_def:
  entry_output_types env return_types kind st vs =
    if kind = FallbackEntry then fallback_output st vs
    else case encoded_runtime_values env st return_types vs of
      (INL (data, spill), st1) =>
        (INL data, let q = FST (memory_load 64 st1) in
                   memory_write (q + LENGTH data) spill (memory_write q data st1))
    | (INR (c, ws), st1) =>
        (INR c, completion_memory c (apply_writes (FST (memory_load 64 st1)) ws st1))
End

Theorem entry_output_types:
  MAP SND p.return_bindings = return_types ⇒
  entry_output env p kind st vs = entry_output_types env return_types kind st vs
Proof
  strip_tac >> simp[entry_output_def, entry_output_types_def]
QED

Theorem call_contract_selector_hit:
  4 ≤ LENGTH fr.call_data ∧
  lookup_external (TAKE 4 fr.call_data) prog.external_functions = SOME e ∧
  (e.payable ∨ fr.call_value = 0) ∧
  lookup_procedure (core_program_environment prog) e.external_procedure = SOME p ∧
  decode_arguments (core_program_environment prog) (MAP SND p.parameters)
    (DROP 4 fr.call_data) 4 128 = INL args ⇒
  call_contract fuel prog imm fr w =
  run_entry fuel (core_program_environment prog) p args fr w (SOME imm) 0 NONE CallEntry
Proof
  strip_tac >> irule call_contract_dispatch_call >>
  metis_tac[dispatch_selector_hit]
QED

Theorem call_entry_frame_return:
  entry_memory 0 NONE
    <| world := w; frame := fr; immutables := imm; scopes := [];
       memory := FEMPTY; memory_size := 0;
       targets := FEMPTY; return_data := SOME [] |> = INL st0 ∧
  materialize_arguments env (MAP SND p.parameters) args st0 =
    INL (values, st1) ∧
  invoke_source fuel env p.procedure_id values st1 gas = r ∧
  finish_source_frame w r.state.world r.completion = FrameSuccess vs w' ∧
  r.unused_gas_evidence = [] ∧
  entry_output env p CallEntry r.state vs = (INL data, st') ⇒
  run_entry_frame fuel env p args fr w imm 0 NONE CallEntry gas =
    (ContractReturned data (settle_source_world w'), memory_image st')
Proof
  strip_tac >> simp[run_entry_frame_def]
QED

Theorem call_contract_nonpayable:
  4 ≤ LENGTH fr.call_data ∧
  lookup_external (TAKE 4 fr.call_data) prog.external_functions = SOME e ∧
  ¬e.payable ∧ fr.call_value ≠ 0 ⇒
  call_contract fuel prog imm fr w = ContractReverted [] w
Proof
  rw[call_contract_def, call_contract_with_gas_thm, dispatch_def,
     unconsumed_gas_result_def]
QED

Theorem call_contract_selector_miss:
  (4 ≤ LENGTH fr.call_data ⇒
   lookup_external (TAKE 4 fr.call_data) prog.external_functions = NONE) ∧
  prog.receive_procedure = NONE ∧ prog.fallback_procedure = NONE ⇒
  call_contract fuel prog imm fr w = ContractReverted [] w
Proof
  rw[call_contract_def, call_contract_with_gas_thm, dispatch_def,
     unconsumed_gas_result_def] >>
  Cases_on ‘fr.call_data’ >> gvs[unconsumed_gas_result_def]
QED

Theorem call_contract_decode_panic:
  4 ≤ LENGTH fr.call_data ∧
  lookup_external (TAKE 4 fr.call_data) prog.external_functions = SOME e ∧
  (e.payable ∨ fr.call_value = 0) ∧
  lookup_procedure (core_program_environment prog) e.external_procedure = SOME p ∧
  decode_arguments (core_program_environment prog) (MAP SND p.parameters)
    (DROP 4 fr.call_data) 4 128 = INR (PanicCompletion n) ⇒
  call_contract fuel prog imm fr w = ContractReverted (panic_data n) w
Proof
  rw[call_contract_def, call_contract_with_gas_thm, dispatch_def,
     unconsumed_gas_result_def] >> fs[unconsumed_gas_result_def]
QED

(* The call prologue writes the free-memory pointer before argument
 * materialization. From empty memory its size is 96 bytes. *)
Theorem entry_memory_call:
  entry_memory 0 NONE st =
    INL (st with <|
      memory := yul_mem_write st.memory 64 (word_to_bytes_be (128w : bytes32));
      memory_size := MAX st.memory_size 96 |>)
Proof
  ‘num_to_bytes 32 128 = word_to_bytes_be (128w : bytes32)’ by
    EVAL_TAC >>
  simp[entry_memory_def, memory_store_def, memory_write_def, memory_touch_def,
       touched_size_def, word_size_def, word_to_bytes_be_def,
       EVAL “word_to_bytes (128w : bytes32) T = []”]
QED

Theorem elementary_abi_layout:
  is_elementary_type ty ⇒
  abi_type env fuel ty = abi_type env 0 ty ∧
  ¬is_dynamic (abi_type env 0 ty) ∧
  static_length (abi_type env 0 ty) = 32 ∧
  abi_stride env ty = 32
Proof
  Cases_on ‘ty’ >>
  simp[abi_type_def, abi_stride_def]
QED

Triviality elementary_abi_word:
  is_elementary_type ty ∧ has_type (abi_type env 0 ty) a ⇒
  LENGTH (enc (abi_type env 0 ty) a) = 32 ∧
  valid_enc (abi_type env 0 ty) (enc (abi_type env 0 ty) a) ∧
  dec (abi_type env 0 ty) (enc (abi_type env 0 ty) a) = a
Proof
  strip_tac >>
  drule elementary_abi_layout >> strip_tac >>
  ‘LENGTH (enc (abi_type env 0 ty) a) = 32’ by
    metis_tac[CONJUNCT1 enc_has_static_length] >>
  ‘LENGTH (enc (abi_type env 0 ty) a) < dimword(:256)’ by
    simp[dimword_def] >>
  simp[] >>
  metis_tac[CONJUNCT1 enc_valid, CONJUNCT1 dec_enc, APPEND_NIL]
QED

Triviality decode_elementary_word:
  is_elementary_type ty ∧ a = abi_type env 0 ty ∧
  abi_runtime_value ty (dec a word) = SOME (ScalarValue s) ∧
  valid_enc a word ∧ pos + 32 ≤ input_len ∧ input_bytes bs pos 32 = word ⇒
  decode_abi_argument env ty bs input_len bound pos arg_base free reach =
    INL (ScalarValue s, free, MAX reach (pos + 32))
Proof
  strip_tac >> Cases_on ‘ty’ >> fs[] >>
  simp[decode_abi_argument_def] >>
  simp[Once (CONJUNCT1 decode_memory_value_def), byte_sequence_type_def] >>
  gvs[abi_type_def]
QED

Triviality input_bytes_word:
  LENGTH word = 32 ⇒ input_bytes (prefix ++ word ++ suffix) (LENGTH prefix) 32 = word
Proof
  rw[input_bytes_def, DROP_APPEND, TAKE_APPEND1, TAKE_LENGTH_ID_rwt]
QED

(* The cumulative head bound and decoder position grow by one word per
 * elementary argument. The input may have trailing bytes. *)
Triviality decode_elementary_arguments:
  ∀args prefix suffix reach.
    EVERY (λ(ty,a,s). is_elementary_type ty ∧
      has_type (abi_type env 0 ty) a ∧ abi_runtime_value ty a = SOME (ScalarValue s)) args ∧
    LENGTH prefix + 32 * LENGTH args ≤ input_len ⇒
    ∃reach'.
      decode_abi_arguments env (MAP FST args)
        (prefix ++ FLAT (MAP (λ(ty,a,s). enc (abi_type env 0 ty) a) args) ++ suffix)
        input_len bound (LENGTH prefix) arg_base free reach =
      INL (MAP (λ(ty,a,s). ScalarValue s) args, reach')
Proof
  Induct_on ‘args’ >>
  simp[decode_abi_arguments_def] >>
  gen_tac >> PairCases_on ‘h’ >> rw[] >>
  drule_all elementary_abi_word >> strip_tac >>
  drule elementary_abi_layout >> strip_tac >>
  rewrite_tac[GSYM APPEND_ASSOC] >>
  qabbrev_tac ‘word = enc (abi_type env 0 h0) h1’ >>
  qabbrev_tac ‘rest = FLAT (MAP (λ(ty,a,s). enc (abi_type env 0 ty) a) args) ++ suffix’ >>
  ‘LENGTH prefix + 32 + 32 * LENGTH args ≤ input_len’ by
    (fs[MULT_CLAUSES] >> decide_tac) >>
  ‘LENGTH prefix + 32 ≤ input_len’ by decide_tac >>
  ‘decode_abi_argument env h0 (prefix ++ (word ++ rest)) input_len bound
      (LENGTH prefix) arg_base free reach =
    INL (ScalarValue h2, free, MAX reach (LENGTH prefix + 32))’ by
    (irule decode_elementary_word >> simp[APPEND_ASSOC, input_bytes_word]) >>
  simp[] >>
  first_x_assum (qspecl_then
    [‘prefix ++ word’, ‘suffix’, ‘MAX reach (LENGTH prefix + 32)’] mp_tac) >>
  simp[APPEND_ASSOC, Abbr‘rest’] >>
  strip_tac >> simp[]
QED

Triviality elementary_head_lengths:
  ∀tys offset.
    EVERY is_elementary_type tys ⇒
    head_lengths (abi_types env fuel tys) offset = offset + 32 * LENGTH tys
Proof
  Induct >> simp[CONJUNCT2 abi_type_def, head_lengths_def] >>
  rw[] >> drule elementary_abi_layout >> strip_tac >>
  simp[MULT_CLAUSES]
QED

Theorem decode_arguments_elementary:
  EVERY (λ(ty, a, s). is_elementary_type ty ∧
    has_type (abi_type env 0 ty) a ∧ abi_runtime_value ty a = SOME (ScalarValue s)) args ⇒
  decode_arguments env (MAP FST args)
    (FLAT (MAP (λ(ty,a,s). enc (abi_type env 0 ty) a) args) ++ suffix) arg_base free =
  INL (MAP (λ(ty,a,s). ScalarValue s) args)
Proof
  strip_tac >>
  ‘EVERY is_elementary_type (MAP FST args) ∧
   LENGTH (FLAT (MAP (λ(ty,a,s). enc (abi_type env 0 ty) a) args)) =
     32 * LENGTH args’ by
    (pop_assum mp_tac >> Induct_on ‘args’ >> simp[] >>
     gen_tac >> PairCases_on ‘h’ >> rw[] >> drule_all elementary_abi_word >>
     simp[MULT_CLAUSES]) >>
  simp[decode_arguments_def, decode_input_def, elementary_head_lengths] >>
  qmatch_goalsub_abbrev_tac ‘decode_abi_arguments _ _ _ input_len’ >>
  mp_tac (Q.INST [‘input_len’ |-> ‘input_len’, ‘bound’ |-> ‘input_len’]
    (Q.SPECL [‘args’, ‘[]’, ‘suffix’, ‘0’] decode_elementary_arguments)) >>
  simp[Abbr‘input_len’] >> strip_tac >> simp[]
QED

Triviality runtime_abi_value_elementary:
  is_elementary_type ty ∧ abi_value ty (ScalarValue s) = SOME a ⇒
  runtime_abi_value env reach st ty (ScalarValue s) =
    (INL (a, enc (abi_type env 0 ty) a, []), reach, st)
Proof
  Cases_on ‘ty’ >>
  simp[runtime_abi_value_def, value_abi_value_def, abi_type_def] >>
  Cases_on ‘a’ >> simp[abi_spill_def]
QED

Triviality runtime_abi_values_elementary:
  ∀args.
    EVERY (λ(ty,a,s). is_elementary_type ty ∧ abi_value ty (ScalarValue s) = SOME a) args ⇒
    runtime_abi_values env reach st (MAP FST args) (MAP (λ(ty,a,s). ScalarValue s) args) =
      (INL (MAP (λ(ty,a,s). (abi_type env 0 ty, enc (abi_type env 0 ty) a)) args, NONE),
       reach, st)
Proof
  Induct >> simp[runtime_abi_values_def] >>
  gen_tac >> PairCases_on ‘h’ >> rw[] >>
  drule_all runtime_abi_value_elementary >> strip_tac >>
  drule elementary_abi_layout >> strip_tac >>
  simp[later_spill_def]
QED

Triviality encoded_elementary_parts:
  ∀args hl tl.
    EVERY (is_elementary_type o FST) args ⇒
    encoded_abi_parts hl tl
      (MAP (λ(ty,a,s). (abi_type env 0 ty, enc (abi_type env 0 ty) a)) args) =
    (FLAT (MAP (λ(ty,a,s). enc (abi_type env 0 ty) a) args), [])
Proof
  Induct >> simp[encoded_abi_parts_def] >>
  gen_tac >> PairCases_on ‘h’ >> rw[] >>
  drule elementary_abi_layout >> strip_tac >> simp[encoded_abi_parts_def]
QED

Theorem memory_write_empty:
  memory_write p [] st = st
Proof
  simp[solidityStateTheory.source_state_component_equality, memory_write_def,
       memory_touch_def, touched_size_def, yul_mem_write_def, MAX_0]
QED

(* No elementary value reads memory during encoding or writes a spill.
 * The returned bytes are written at the free-memory pointer. *)
Theorem entry_output_elementary:
  MAP SND p.return_bindings = MAP FST args ∧
  EVERY (λ(ty,a,s). is_elementary_type ty ∧ abi_value ty (ScalarValue s) = SOME a) args ⇒
  entry_output env p CallEntry st (MAP (λ(ty,a,s). ScalarValue s) args) =
    (INL (FLAT (MAP (λ(ty,a,s). enc (abi_type env 0 ty) a) args)),
     memory_write (FST (memory_load 64 st))
       (FLAT (MAP (λ(ty,a,s). enc (abi_type env 0 ty) a) args)) st)
Proof
  strip_tac >>
  ‘EVERY (is_elementary_type o FST) args’ by
    (qpat_x_assum ‘EVERY _ args’ mp_tac >>
     simp[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
  simp[entry_output_def, encoded_runtime_values_def, runtime_abi_values_elementary,
       encoder_state_def, guard_result_def, encoded_abi_tuple_def, encoded_elementary_parts,
       memory_write_empty]
QED

(* These rules provide the ABI value for either direction of the codec and
 * the exact bytes for one slot of the elementary argument or return list. *)
Theorem abi_address_word:
  has_type Address (NumV (w2n (a : address))) ∧
  abi_runtime_value (AddressT m) (NumV (w2n a)) = SOME (ScalarValue (AddressValue a)) ∧
  abi_value (AddressT m) (ScalarValue (AddressValue a)) = SOME (NumV (w2n a)) ∧
  enc Address (NumV (w2n a)) = word_to_bytes_be (w2w a : bytes32)
Proof
  simp[abi_runtime_value_def, abi_value_def, word_to_bytes_be_def, w2w_def] >>
  mp_tac (ISPEC “a : address” w2n_lt) >> simp[dimword_def]
QED

Theorem abi_uint_word:
  valid_int_bound n ∧ v < 2 ** n ⇒
  has_type (Uint n) (NumV v) ∧
  abi_runtime_value (UintT n) (NumV v) = SOME (ScalarValue (IntegerValue (&v))) ∧
  abi_value (UintT n) (ScalarValue (IntegerValue (&v))) = SOME (NumV v) ∧
  enc (Uint n) (NumV v) = word_to_bytes_be (n2w v : bytes32)
Proof
  simp[abi_runtime_value_def, abi_value_def, word_to_bytes_be_def]
QED

Theorem abi_int_word:
  valid_int_bound n ∧ int_bits_bound i n ⇒
  has_type (Int n) (IntV i) ∧
  abi_runtime_value (IntT n) (IntV i) = SOME (ScalarValue (IntegerValue i)) ∧
  abi_value (IntT n) (ScalarValue (IntegerValue i)) = SOME (IntV i) ∧
  enc (Int n) (IntV i) = word_to_bytes_be (i2w i : bytes32)
Proof
  simp[abi_runtime_value_def, abi_value_def, word_to_bytes_be_def]
QED

Theorem abi_bool_word:
  has_type Bool (NumV (if b then 1 else 0)) ∧
  abi_runtime_value BoolT (NumV (if b then 1 else 0)) = SOME (ScalarValue (BoolValue b)) ∧
  abi_value BoolT (ScalarValue (BoolValue b)) = SOME (NumV (if b then 1 else 0)) ∧
  enc Bool (NumV (if b then 1 else 0)) = word_to_bytes_be (b2w b : bytes32)
Proof
  Cases_on ‘b’ >> simp[abi_runtime_value_def, abi_value_def, word_to_bytes_be_def]
QED

Theorem abi_fixed_bytes_word:
  0 < n ∧ n ≤ 32 ∧ LENGTH bs = n ⇒
  has_type (Bytes (SOME n)) (BytesV bs) ∧
  abi_runtime_value (FixedBytesT n) (BytesV bs) = SOME (ScalarValue (BytesValue bs)) ∧
  abi_value (FixedBytesT n) (ScalarValue (BytesValue bs)) = SOME (BytesV bs) ∧
  enc (Bytes (SOME n)) (BytesV bs) = bs ++ REPLICATE (32 - n) 0w
Proof
  rw[abi_runtime_value_def, abi_value_def, TAKE_LENGTH_TOO_LONG, dimword_def]
QED
