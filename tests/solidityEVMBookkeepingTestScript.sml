(* Nonempty bookkeeping and distinct transaction-original/current storage.
 * These finite witnesses complement, not replace, general preservation laws.
 *)
Theory solidityEVMBookkeepingTest
Ancestors
  solidityEVMFrameTest solidityEVMCallTest solidityEVMCall
  vfmContext vfmState vfmExecution vfmExecutionProp vfmOperation
  vfmConstants combin
Libs
  cv_transLib wordsLib

Definition bookkeeping_fixture_def:
  bookkeeping_fixture child_code =
    let es = nested_call_fixture in
    let account = lookup_account 0x200w es.rollback.accounts in
    let current_storage = update_storage 0w 9w
      (update_storage 1w 88w empty_storage) in
    let original_storage = update_storage 0w 5w
      (update_storage 1w 88w empty_storage) in
    let seeded = es.rollback with <|
      accounts := update_account 0x200w
        (account with <| code := child_code; storage := current_storage |>)
        es.rollback.accounts;
      tStorage := update_transient_storage 0x300w
        (update_storage 7w 42w empty_storage) empty_transient_storage;
      accesses := <| addresses := fINSERT 0x300w fEMPTY;
                     storageKeys := fINSERT (SK 0x200w 0w)
                       (fINSERT (SK 0x300w 7w) fEMPTY) |>;
      toDelete := [0x400w]
    |> in
    let original = seeded with accounts updated_by
      (update_account 0x200w
        (account with <| code := child_code; storage := original_storage |>)) in
    let contexts = case es.contexts of
      [(caller, old_checkpoint); (parent, old_original)] =>
        [(caller, seeded); (parent, original)]
    | _ => [] in
    es with <|
      contexts := contexts; rollback := seeded;
      msdomain := Collect <| addresses := fINSERT 0x300w fEMPTY;
        storageKeys := fINSERT (SK 0x300w 7w) fEMPTY;
        fullStorages := fINSERT 0x300w fEMPTY |>
    |>
End

val () = cv_auto_trans bookkeeping_fixture_def;

Definition bookkeeping_summary_def:
  bookkeeping_summary child_code =
    let es = bookkeeping_fixture child_code in
    case invoke_boundary BoundaryCall es of
      BoundaryReturned flag data final =>
        (case final.contexts of
          [(caller, saved); (parent, original)] =>
            (case final.msdomain of
              Enforce dom => NONE
            | Collect dom => SOME
              (flag,
               w2n (lookup_storage 0w (lookup_account 0x200w final.rollback.accounts).storage),
               w2n (lookup_storage 0w (lookup_account 0x200w saved.accounts).storage),
               w2n (lookup_storage 0w (lookup_account 0x200w original.accounts).storage),
               w2n (lookup_storage 1w (lookup_account 0x200w final.rollback.accounts).storage),
               w2n (lookup_storage 7w (lookup_transient_storage 0x300w final.rollback.tStorage)),
               final.rollback.toDelete = [0x400w],
               fIN 0x300w final.rollback.accesses.addresses,
               fIN (SK 0x300w 7w) final.rollback.accesses.storageKeys,
               fIN 0x200w final.rollback.accesses.addresses,
               fIN (SK 0x200w 0w) final.rollback.accesses.storageKeys,
               fIN 0x300w dom.addresses ∧ fIN (SK 0x300w 7w) dom.storageKeys ∧
                 fIN 0x300w dom.fullStorages,
               MAP FST (TL final.contexts) = MAP FST (TL es.contexts),
               final.txParams = es.txParams))
        | _ => NONE)
    | _ => NONE
End

val () = cv_auto_trans bookkeeping_summary_def;

Theorem successful_call_preserves_seeded_bookkeeping:
  bookkeeping_summary [0x60w; 1w; 0x60w; 0w; 0x55w; 0w] =
    SOME (1w, 1, 9, 5, 88, 42, T, T, T, T, T, T, T, T)
Proof
  CONV_TAC cv_eval
QED

Theorem reverted_call_preserves_original_and_saved_bookkeeping:
  bookkeeping_summary [0x60w; 1w; 0x60w; 0w; 0x55w;
                       0x60w; 0w; 0x60w; 0w; 0xfdw] =
    SOME (0w, 9, 9, 5, 88, 42, T, T, T, T, T, T, T, T)
Proof
  CONV_TAC cv_eval
QED

(* Nonempty initial access coverage includes B.slot0, whose current/original
 * contents differ. This fixture does not assume checkpoint account equality.
 *)
Theorem bookkeeping_fixture_well_formed:
  LENGTH child_code ≤ 24576 ⇒ wf_state (bookkeeping_fixture child_code)
Proof
  rw[bookkeeping_fixture_def, nested_call_fixture_def, call_fixture_def,
     call_operands_def, boundary_opcode_def, opcode_def,
     wf_state_def, wf_context_def, all_accounts_def, wf_accounts_def,
     wf_account_state_def, stack_room_ok_def, gas_stack_ok_def,
     outputTo_consistent_stack_def, outputTo_consistent_ctx_def,
     initial_context_def, initial_msg_params_def, fixture_tx_def,
     empty_return_destination_def, update_account_def, lookup_account_def,
     empty_accounts_def, empty_account_state_def, stack_limit_def,
     context_limit_def, APPLY_UPDATE_THM]
  \\ rw[]
  \\ Cases_on ‘i’
  \\ fs[unused_gas_def]
QED
