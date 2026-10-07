(* Executable concrete EVM boundary witnesses, not Solidity conformance tests. *)
Theory solidityEVMCallTest
Ancestors
  solidityEVMCall vfmExecutionProp vfmContext vfmState vfmConstants combin
Libs
  cv_transLib wordsLib

Definition fixture_tx_def:
  fixture_tx = <|
    from := 0x1000w; to := SOME 0x1001w; data := [];
    nonce := 0; value := 0; gasLimit := 200000; gasPrice := 0;
    accessList := []; blobVersionedHashes := [];
    maxFeePerBlobGas := NONE; maxFeePerGas := NONE;
    authorizationList := []
  |>
End

val () = cv_auto_trans fixture_tx_def;

Definition fixture_tx_params_def:
  fixture_tx_params = <|
    origin := 0x1000w; gasPrice := 0; baseFeePerGas := 0;
    baseFeePerBlobGas := 0; blockNumber := 1; blockTimeStamp := 1;
    blockCoinBase := 0x1000w; blockGasLimit := 1000000;
    prevRandao := 0w; prevHashes := []; blobHashes := [];
    chainId := 1; authRefund := 0
  |>
End

val () = cv_auto_trans fixture_tx_params_def;

Definition call_fixture_def:
  call_fixture instruction child_code operands input suffix =
    let caller_code = opcode (boundary_opcode instruction) ++ suffix in
    let accounts = update_account 0x1001w
      (empty_account_state with <| balance := 1000; code := caller_code |>)
      (update_account 0x200w
        (empty_account_state with code := child_code) empty_accounts) in
    let checkpoint = <|
      accounts := accounts; tStorage := empty_transient_storage;
      accesses := <| addresses := fEMPTY; storageKeys := fEMPTY |>;
      toDelete := []
    |> in
    let caller = initial_context 0x1001w caller_code F
      empty_return_destination fixture_tx
      with <| stack := operands; memory := input |> in
    <| contexts := [(caller, checkpoint)];
       txParams := fixture_tx_params; rollback := checkpoint;
       msdomain := Collect empty_domain |>
End

val () = cv_auto_trans call_fixture_def;

Theorem call_fixture_well_formed:
  LENGTH child_code ≤ 24576 ∧
  LENGTH (opcode (boundary_opcode instruction) ++ suffix) ≤ 24576 ∧
  LENGTH operands ≤ 1024 ⇒
  wf_state (call_fixture instruction child_code operands input suffix)
Proof
  rw[call_fixture_def, wf_state_def, wf_context_def, all_accounts_def,
     wf_accounts_def, wf_account_state_def, stack_room_ok_def,
     gas_stack_ok_def, outputTo_consistent_stack_def,
     outputTo_consistent_ctx_def, initial_context_def, initial_msg_params_def,
     fixture_tx_def, empty_return_destination_def, update_account_def,
     empty_accounts_def, empty_account_state_def, stack_limit_def,
     context_limit_def, APPLY_UPDATE_THM]
  \\ rw[]
QED

Definition call_operands_def:
  call_operands = [65535w; 0x200w; 0w; 0w; 0w; 0w; 1w] : bytes32 list
End

val () = cv_auto_trans call_operands_def;

(* Executable summaries use finite observations, not account-function equality.
 * General checkpoint preservation needs a separate theorem with wf hypotheses.
 *)
Definition finite_call_summary_def:
  finite_call_summary instruction es =
    case invoke_boundary instruction es of
      BoundaryReturned word data final =>
        (case final.contexts of
          [] => NONE
        | (ctxt, checkpoint)::rest => SOME
          (word, data, ctxt.memory, ctxt.pc, LENGTH final.contexts,
           w2n (lookup_storage 0w (lookup_account 0x200w final.rollback.accounts).storage),
           w2n (lookup_storage 0w (lookup_account 0x1001w final.rollback.accounts).storage),
           final.txParams = es.txParams))
    | _ => NONE
End

val () = cv_auto_trans finite_call_summary_def;

Theorem call_returns_without_running_suffix:
  finite_call_summary BoundaryCall
    (call_fixture BoundaryCall
      [0x60w; 0x2aw; 0x60w; 0w; 0x53w; 0x60w; 1w; 0x60w; 0w; 0xf3w]
      call_operands [] [0xfew]) =
    SOME (1w, [0x2aw], [0x2aw] ++ REPLICATE 31 0w, 1, 1, 0, 0, T)
Proof
  CONV_TAC cv_eval
QED

Theorem call_revert_keeps_data_and_restores_storage:
  finite_call_summary BoundaryCall
    (call_fixture BoundaryCall
      [0x60w; 1w; 0x60w; 0w; 0x55w;
       0x60w; 0x2aw; 0x60w; 0w; 0x53w; 0x60w; 1w; 0x60w; 0w; 0xfdw]
      call_operands [] [0w]) =
    SOME (0w, [0x2aw], [0x2aw] ++ REPLICATE 31 0w, 1, 1, 0, 0, T)
Proof
  CONV_TAC cv_eval
QED

Theorem call_success_keeps_storage:
  finite_call_summary BoundaryCall
    (call_fixture BoundaryCall [0x60w; 1w; 0x60w; 0w; 0x55w; 0w]
      call_operands [] [0w]) =
    SOME (1w, [], REPLICATE 32 0w, 1, 1, 1, 0, T)
Proof
  CONV_TAC cv_eval
QED

Theorem call_exception_is_failed_call_not_adapter_abort:
  finite_call_summary BoundaryCall
    (call_fixture BoundaryCall [0xfew] call_operands [] [0w]) =
    SOME (0w, [], REPLICATE 32 0w, 1, 1, 0, 0, T)
Proof
  CONV_TAC cv_eval
QED

Theorem static_call_rejects_write:
  finite_call_summary BoundaryStaticCall
    (call_fixture BoundaryStaticCall [0x60w; 1w; 0x60w; 0w; 0x55w; 0w]
      [65535w; 0x200w; 0w; 0w; 0w; 1w] [] [0w]) =
    SOME (0w, [], REPLICATE 32 0w, 1, 1, 0, 0, T)
Proof
  CONV_TAC cv_eval
QED

Theorem delegate_call_writes_callers_storage:
  finite_call_summary BoundaryDelegateCall
    (call_fixture BoundaryDelegateCall [0x60w; 1w; 0x60w; 0w; 0x55w; 0w]
      [65535w; 0x200w; 0w; 0w; 0w; 1w] [] [0w]) =
    SOME (1w, [], REPLICATE 32 0w, 1, 1, 0, 1, T)
Proof
  CONV_TAC cv_eval
QED

Theorem empty_code_call_succeeds:
  finite_call_summary BoundaryCall
    (call_fixture BoundaryCall [] call_operands [] [0w]) =
    SOME (1w, [], REPLICATE 32 0w, 1, 1, 0, 0, T)
Proof
  CONV_TAC cv_eval
QED

Theorem insufficient_balance_is_failed_call:
  finite_call_summary BoundaryCall
    (call_fixture BoundaryCall []
      [65535w; 0x200w; 1001w; 0w; 0w; 0w; 1w] [] [0xfew]) =
    SOME (0w, [], REPLICATE 32 0w, 1, 1, 0, 0, T)
Proof
  CONV_TAC cv_eval
QED

Definition value_transfer_summary_def:
  value_transfer_summary =
    let es = call_fixture BoundaryCall []
      [65535w; 0x200w; 7w; 0w; 0w; 0w; 1w] [] [0xfew] in
    case invoke_boundary BoundaryCall es of
      BoundaryReturned word data final => SOME
        (word, (lookup_account 0x1001w final.rollback.accounts).balance,
         (lookup_account 0x200w final.rollback.accounts).balance)
    | _ => NONE
End

val () = cv_auto_trans value_transfer_summary_def;

Theorem successful_call_transfers_value_once:
  value_transfer_summary = SOME (1w, 993, 7)
Proof
  CONV_TAC cv_eval
QED

Definition domain_abort_summary_def:
  domain_abort_summary =
    let es = call_fixture BoundaryCall [] call_operands [] [0xfew]
      with msdomain := Enforce empty_domain in
    case invoke_boundary BoundaryCall es of
      BoundaryAborted (SOME (OutsideDomain (INL addr))) final =>
        SOME (addr, LENGTH final.contexts)
    | _ => NONE
End

val () = cv_auto_trans domain_abort_summary_def;

Theorem domain_error_is_not_a_failed_call:
  domain_abort_summary = SOME (0x200w, 1)
Proof
  CONV_TAC cv_eval
QED

Theorem wrong_opcode_is_rejected:
  invoke_boundary BoundaryStaticCall
    (call_fixture BoundaryCall [] call_operands [] [0w]) =
    BoundaryWrongPosition
Proof
  CONV_TAC cv_eval
QED

Theorem precompile_completion_does_not_run_caller:
  finite_call_summary BoundaryCall
    (call_fixture BoundaryCall []
      [65535w; 4w; 0w; 0w; 1w; 32w; 1w] [0x2aw] [0xfew]) =
    SOME (1w, [0x2aw], [0x2aw] ++ REPLICATE 31 0w ++
      [0x2aw] ++ REPLICATE 31 0w, 1, 1, 0, 0, T)
Proof
  CONV_TAC cv_eval
QED
