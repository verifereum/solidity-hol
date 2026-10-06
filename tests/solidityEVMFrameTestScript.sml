(* Genuine nested concrete frames, not invented source-frame EVM registers. *)
Theory solidityEVMFrameTest
Ancestors
  solidityEVMCallTest solidityEVMCall vfmOperation
  vfmExecutionProp vfmContext vfmState vfmConstants combin
Libs
  cv_transLib wordsLib

Definition nested_call_fixture_def:
  nested_call_fixture =
    let es = call_fixture BoundaryCall [0x60w; 1w; 0x60w; 0w; 0x55w; 0w]
      call_operands [] [0x60w; 0w; 0x60w; 0w; 0xfdw] in
    let parent = initial_context 0x1000w [0xf1w; 0w] F
      empty_return_destination
      (fixture_tx with <| to := SOME 0x1000w; gasLimit := 500000 |>)
      with gasUsed := 200000 in
    es with contexts := es.contexts ++ [(parent, es.rollback)]
End

val () = cv_auto_trans nested_call_fixture_def;

Theorem nested_call_fixture_well_formed:
  wf_state nested_call_fixture
Proof
  rw[nested_call_fixture_def, call_fixture_def, call_operands_def,
     boundary_opcode_def, opcode_def, wf_state_def, wf_context_def,
     all_accounts_def, wf_accounts_def, wf_account_state_def,
     stack_room_ok_def, gas_stack_ok_def, outputTo_consistent_stack_def,
     outputTo_consistent_ctx_def, initial_context_def, initial_msg_params_def,
     fixture_tx_def, empty_return_destination_def, update_account_def,
     empty_accounts_def, empty_account_state_def, stack_limit_def,
     context_limit_def, APPLY_UPDATE_THM]
  \\ rw[]
  \\ Cases_on ‘i’
  \\ fs[unused_gas_def]
QED

Definition caller_entry_oog_fixture_def:
  caller_entry_oog_fixture = nested_call_fixture with <|
    contexts updated_by
      (λcontexts. case contexts of
         [] => []
       | (ctxt, checkpoint)::rest =>
           (ctxt with gasUsed := 199999, checkpoint)::rest);
    rollback updated_by (λrb. rb with accounts updated_by
      (λaccounts. update_account 0x200w
        (lookup_account 0x200w accounts with storage :=
          update_storage 0w 9w empty_storage) accounts))
  |>
End

val () = cv_auto_trans caller_entry_oog_fixture_def;

Definition caller_entry_oog_summary_def:
  caller_entry_oog_summary =
    case invoke_boundary BoundaryCall caller_entry_oog_fixture of
      BoundaryCallerExited final =>
        (case final.contexts of
           [] => NONE
         | (ctxt, checkpoint)::rest => SOME
             (ctxt.stack, ctxt.pc, ctxt.returnData, LENGTH final.contexts,
              w2n (lookup_storage 0w
                (lookup_account 0x200w caller_entry_oog_fixture.rollback.accounts).storage),
              w2n (lookup_storage 0w
                (lookup_account 0x200w final.rollback.accounts).storage),
              final.txParams = caller_entry_oog_fixture.txParams))
    | _ => NONE
End

val () = cv_auto_trans caller_entry_oog_summary_def;

Theorem caller_entry_out_of_gas_exits_to_parent:
  caller_entry_oog_summary = SOME ([0w], 1, [], 1, 9, 0, T)
Proof
  CONV_TAC cv_eval
QED

Definition outer_rollback_summary_def:
  outer_rollback_summary es =
    case execute_boundary BoundaryCall es of
      SOME (INL (), resumed) =>
        (case run_call resumed of
          SOME (INL (), final) =>
            (case final.contexts of
              [] => NONE
            | (ctxt, checkpoint)::rest => SOME
                (w2n (lookup_storage 0w (lookup_account 0x200w resumed.rollback.accounts).storage),
                 w2n (lookup_storage 0w (lookup_account 0x200w final.rollback.accounts).storage),
                 ctxt.stack, ctxt.returnData, LENGTH final.contexts,
                 final.txParams = es.txParams))
        | _ => NONE)
    | _ => NONE
End

val () = cv_auto_trans outer_rollback_summary_def;

Theorem outer_revert_undoes_successful_inner_call:
  outer_rollback_summary nested_call_fixture = SOME (1, 0, [0w], [], 1, T)
Proof
  CONV_TAC cv_eval
QED

(* Both calls read the previous transient value, store 7, and return the old
 * value. The harness supplies the second operand stack without resetting any
 * transaction bookkeeping; it is not a compiled source-program simulation.
 *)
Definition two_calls_transient_summary_def:
  two_calls_transient_summary =
    let es = call_fixture BoundaryCall
      [0x60w; 0w; 0x5cw; 0x60w; 0w; 0x53w;
       0x60w; 7w; 0x60w; 0w; 0x5dw;
       0x60w; 1w; 0x60w; 0w; 0xf3w]
      call_operands [] [0xf1w; 0xfew] in
    case execute_boundary BoundaryCall es of
      SOME (INL (), resumed) =>
        let next = resumed with <|
          contexts updated_by (λcontexts.
            case contexts of
              [] => []
            | (ctxt, checkpoint)::rest =>
                (ctxt with stack := call_operands, checkpoint)::rest)
        |> in
        (case invoke_boundary BoundaryCall next of
          BoundaryReturned word data final => SOME
            (word, data,
             w2n (lookup_storage 0w (lookup_transient_storage 0x200w final.rollback.tStorage)),
             final.txParams = es.txParams)
        | _ => NONE)
    | _ => NONE
End

val () = cv_auto_trans two_calls_transient_summary_def;

Theorem sequential_calls_preserve_transient_storage:
  two_calls_transient_summary = SOME (1w, [7w], 7, T)
Proof
  CONV_TAC cv_eval
QED
