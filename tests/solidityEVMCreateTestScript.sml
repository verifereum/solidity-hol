Theory solidityEVMCreateTest
Ancestors
  solidityEVMCallTest
Libs
  cv_transLib wordsLib

Definition creation_summary_def:
  creation_summary instruction es =
    case invoke_boundary instruction es of
      BoundaryReturned word data final =>
        let created = address_for_create 0x1001w 0 in
        SOME (word, data,
          (lookup_account 0x1001w final.rollback.accounts).nonce,
          (lookup_account created final.rollback.accounts).code,
          LENGTH final.contexts)
    | _ => NONE
End

val () = cv_auto_trans creation_summary_def;

Theorem create_installs_runtime_code:
  creation_summary BoundaryCreate
    (call_fixture BoundaryCreate [] [0w; 0w; 10w]
      [0x60w; 0w; 0x60w; 0w; 0x53w; 0x60w; 1w; 0x60w; 0w; 0xf3w]
      [0xfew]) =
    SOME (w2w (address_for_create 0x1001w 0), [], 1, [0w], 1)
Proof
  CONV_TAC cv_eval
QED

Theorem create_revert_retains_creator_nonce:
  creation_summary BoundaryCreate
    (call_fixture BoundaryCreate [] [0w; 0w; 5w]
      [0x60w; 0w; 0x60w; 0w; 0xfdw] [0xfew]) =
    SOME (0w, [], 1, [], 1)
Proof
  CONV_TAC cv_eval
QED

Definition collision_fixture_def:
  collision_fixture =
    let es = call_fixture BoundaryCreate [] [0w; 0w; 0w] [] [0xfew] in
    es with rollback updated_by (λrb. rb with accounts updated_by
      (update_account (address_for_create 0x1001w 0)
        (empty_account_state with nonce := 1)))
End

val () = cv_auto_trans collision_fixture_def;

Theorem create_collision_retains_creator_nonce:
  creation_summary BoundaryCreate collision_fixture = SOME (0w, [], 1, [], 1)
Proof
  CONV_TAC cv_eval
QED

Definition create2_summary_def:
  create2_summary code es =
    case invoke_boundary BoundaryCreate2 es of
      BoundaryReturned word data final =>
        let created = address_for_create2 0x1001w 42w code in
        SOME (word = w2w created, data,
          (lookup_account 0x1001w final.rollback.accounts).nonce,
          (lookup_account created final.rollback.accounts).code,
          LENGTH final.contexts)
    | _ => NONE
End

val () = cv_auto_trans create2_summary_def;

Theorem create2_uses_salt_and_initcode:
  let code = [0x60w; 0w; 0x60w; 0w; 0x53w; 0x60w; 1w; 0x60w; 0w; 0xf3w] in
  create2_summary code
    (call_fixture BoundaryCreate2 [] [0w; 0w; 10w; 42w] code [0xfew]) =
    SOME (T, [], 1, [0w], 1)
Proof
  CONV_TAC cv_eval
QED

(* A nonce-zero, code-empty target can already have storage. Seed the live,
 * saved and transaction-original accounts alike, before entering CREATE.
 *)
Definition storage_only_target_fixture_def:
  storage_only_target_fixture target es =
    let accounts = update_account target
      (empty_account_state with storage :=
        update_storage 0w 7w (update_storage 1w 9w empty_storage))
      es.rollback.accounts in
    es with <|
      rollback updated_by (λrb. rb with accounts := accounts);
      contexts updated_by
        (MAP (λ(ctxt, rb). (ctxt, rb with accounts := accounts)));
      originalAccounts := accounts
    |>
End

val () = cv_auto_trans storage_only_target_fixture_def;

(* Include the saved and original values: CREATE resets the original account,
 * while the saved account must still be available to roll back the clearing.
 *)
Definition storage_only_creation_summary_def:
  storage_only_creation_summary instruction target es =
    case invoke_boundary instruction es of
      BoundaryReturned word data final =>
        (case final.contexts of
          [] => NONE
        | (ctxt, saved)::rest => SOME
            (word, data, (lookup_account target final.rollback.accounts).nonce,
             lookup_storage 0w (lookup_account target final.rollback.accounts).storage,
             lookup_storage 1w (lookup_account target final.rollback.accounts).storage,
             lookup_storage 0w (lookup_account target saved.accounts).storage,
             lookup_storage 0w (lookup_account target final.originalAccounts).storage,
             ¬fIN (SK target 0w) final.rollback.accesses.storageKeys ∧
               ¬fIN (SK target 1w) final.rollback.accesses.storageKeys,
             ctxt.pc, LENGTH final.contexts))
    | _ => NONE
End

val () = cv_auto_trans storage_only_creation_summary_def;

Theorem create_clears_unaccessed_storage_and_stops_at_boundary:
  storage_only_creation_summary BoundaryCreate (address_for_create 0x1001w 0)
    (storage_only_target_fixture (address_for_create 0x1001w 0)
      (call_fixture BoundaryCreate [] [0w; 0w; 0w] [] [0xfew])) =
    SOME (w2w (address_for_create 0x1001w 0), [], 1, 0w, 0w, 7w, 0w, T, 1, 1)
Proof
  CONV_TAC cv_eval
QED

Theorem create2_clears_unaccessed_storage_and_stops_at_boundary:
  storage_only_creation_summary BoundaryCreate2
    (address_for_create2 0x1001w 42w [])
    (storage_only_target_fixture (address_for_create2 0x1001w 42w [])
      (call_fixture BoundaryCreate2 [] [0w; 0w; 0w; 42w] [] [0xfew])) =
    SOME (w2w (address_for_create2 0x1001w 42w []),
          [], 1, 0w, 0w, 7w, 0w, T, 1, 1)
Proof
  CONV_TAC cv_eval
QED

Theorem create_revert_restores_unaccessed_storage:
  storage_only_creation_summary BoundaryCreate (address_for_create 0x1001w 0)
    (storage_only_target_fixture (address_for_create 0x1001w 0)
      (call_fixture BoundaryCreate [] [0w; 0w; 3w]
        [0x5fw; 0x5fw; 0xfdw] [0xfew])) =
    SOME (0w, [], 0, 7w, 9w, 7w, 0w, T, 1, 1)
Proof
  CONV_TAC cv_eval
QED

Definition creation_outer_rollback_summary_def:
  creation_outer_rollback_summary =
    let target = address_for_create 0x1001w 0 in
    let es = storage_only_target_fixture target
      (call_fixture BoundaryCreate [] [0w; 0w; 0w] []
        [0x5fw; 0x5fw; 0xfdw]) in
    let parent = initial_context 0x1000w [0xf1w; 0w] F
      empty_return_destination
      (fixture_tx with <| to := SOME 0x1000w; gasLimit := 500000 |>)
      with gasUsed := 200000 in
    let nested = es with contexts := es.contexts ++ [(parent, es.rollback)] in
    case execute_boundary BoundaryCreate nested of
      SOME (INL (), resumed) =>
        (case run_call resumed of
          SOME (INL (), final) =>
            (case final.contexts of
              [] => NONE
            | (ctxt, saved)::rest => SOME
                ((lookup_account target resumed.rollback.accounts).nonce,
                 lookup_storage 0w (lookup_account target resumed.rollback.accounts).storage,
                 (lookup_account target final.rollback.accounts).nonce,
                 lookup_storage 0w (lookup_account target final.rollback.accounts).storage,
                 lookup_storage 1w (lookup_account target final.rollback.accounts).storage,
                 lookup_storage 0w (lookup_account target final.originalAccounts).storage,
                 ctxt.stack, ctxt.pc, LENGTH final.contexts))
        | _ => NONE)
    | _ => NONE
End

val () = cv_auto_trans creation_outer_rollback_summary_def;

Theorem outer_revert_undoes_successful_creation_storage_clearing:
  creation_outer_rollback_summary = SOME (1, 0w, 0, 7w, 9w, 0w, [0w], 1, 1)
Proof
  CONV_TAC cv_eval
QED


(* Here the clearing happens inside the CALL subtree, after boundary entry.
 * Its saved checkpoint still has both nonzero, unaccessed slots.
 *)
Theorem call_subtree_creation_clears_unaccessed_storage:
  storage_only_creation_summary BoundaryCall (address_for_create 0x200w 0)
    (storage_only_target_fixture (address_for_create 0x200w 0)
      (call_fixture BoundaryCall [0x5fw; 0x5fw; 0x5fw; 0xf0w; 0w]
        call_operands [] [0xfew])) =
    SOME (1w, [], 1, 0w, 0w, 7w, 0w, T, 1, 1)
Proof
  CONV_TAC cv_eval
QED

Theorem call_subtree_revert_restores_creation_cleared_storage:
  storage_only_creation_summary BoundaryCall (address_for_create 0x200w 0)
    (storage_only_target_fixture (address_for_create 0x200w 0)
      (call_fixture BoundaryCall
        [0x5fw; 0x5fw; 0x5fw; 0xf0w; 0x5fw; 0x5fw; 0xfdw]
        call_operands [] [0xfew])) =
    SOME (0w, [], 0, 7w, 9w, 7w, 0w, T, 1, 1)
Proof
  CONV_TAC cv_eval
QED
