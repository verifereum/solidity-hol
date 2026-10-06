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
