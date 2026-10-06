(* Coherent deployed A/B bytecode: A's outer frame calls B, B calls A's
 * callback branch, then the outer A frame resumes and reads callback storage.
 * No source interpreter is involved in this witness.
 *)
Theory solidityEVMReentryTest
Ancestors
  solidityEVMCallTest solidityEVMCall solidityState
  solidityEVMBoundaryProps vfmRunCall vfmExecutionProp
  vfmContext vfmState vfmOperation vfmConstants combin arithmetic
Libs
  cv_transLib wordsLib

Definition reentry_a_code_def:
  reentry_a_code =
    [0x36w; 0x15w; 0x60w; 11w; 0x57w;
     0x60w; 7w; 0x60w; 0w; 0x55w; 0w;
     0x5bw;
     0x60w; 1w; 0x60w; 0w; 0x60w; 0w; 0x60w; 0w; 0x60w; 0w;
     0x61w; 2w; 0w; 0x61w; 0xffw; 0xffw; 0xf1w;
     0x50w; 0x60w; 0w; 0x54w; 0x60w; 0w; 0x53w;
     0x60w; 1w; 0x60w; 0w; 0xf3w] : byte list
End

val () = cv_auto_trans reentry_a_code_def;

Definition reentry_b_code_def:
  reentry_b_code =
    [0x60w; 1w; 0x60w; 0w; 0x53w;
     0x60w; 0w; 0x60w; 0w; 0x60w; 1w; 0x60w; 0w; 0x60w; 0w;
     0x61w; 0x10w; 1w; 0x61w; 0x75w; 0x30w; 0xf1w; 0x50w; 0w] : byte list
End

val () = cv_auto_trans reentry_b_code_def;

(* Start at an actual outer A invocation, then execute its prefix to CALL.
 * No patched PC or stack and no mismatch between context and deployed code.
 *)
Definition reentry_initial_def:
  reentry_initial =
    let accounts = update_account 0x1001w
      (empty_account_state with <| balance := 1000; code := reentry_a_code |>)
      (update_account 0x200w
        (empty_account_state with code := reentry_b_code) empty_accounts) in
    let checkpoint = <|
      accounts := accounts; tStorage := empty_transient_storage;
      accesses := <| addresses := fEMPTY; storageKeys := fEMPTY |>;
      toDelete := []
    |> in
    <| contexts := [(initial_context 0x1001w reentry_a_code F
          empty_return_destination fixture_tx, checkpoint)];
       txParams := fixture_tx_params; rollback := checkpoint;
       msdomain := Collect empty_domain |>
End

val () = cv_auto_trans reentry_initial_def;

Theorem reentry_initial_well_formed:
  wf_state reentry_initial
Proof
  rw[reentry_initial_def, reentry_a_code_def, reentry_b_code_def,
     wf_state_def, wf_context_def, all_accounts_def, wf_accounts_def,
     wf_account_state_def, stack_room_ok_def, gas_stack_ok_def,
     outputTo_consistent_stack_def, outputTo_consistent_ctx_def,
     initial_context_def, initial_msg_params_def, fixture_tx_def,
     empty_return_destination_def, update_account_def, empty_accounts_def,
     empty_account_state_def, stack_limit_def, context_limit_def,
     APPLY_UPDATE_THM]
  \\ rw[]
QED

Definition reentry_boundary_state_def:
  reentry_boundary_state = SND (FUNPOW (step o SND) 12 (INL (), reentry_initial))
End

val () = cv_auto_trans reentry_boundary_state_def;

Theorem reentry_prefix_reaches_call_normally:
  FST (FUNPOW (step o SND) 12 (INL (), reentry_initial)) = INL () ∧
  positioned_at_boundary BoundaryCall reentry_boundary_state
Proof
  CONV_TAC cv_eval
QED

Theorem reentry_boundary_well_formed:
  wf_state reentry_boundary_state
Proof
  simp[reentry_boundary_state_def]
  \\ irule stepping_preserves_well_formedness
  \\ simp[reentry_initial_well_formed]
QED

Definition reentry_summary_def:
  reentry_summary =
    let es = reentry_boundary_state in
    case invoke_boundary BoundaryCall es of
      BoundaryReturned flag data resumed =>
        (case (project_evm_world es, project_evm_world resumed, run_call resumed) of
          (SOME before, SOME after, SOME (INR NONE, final)) =>
            (case (resumed.contexts, final.contexts) of
              ([(resumed_context, checkpoint)], [(final_context, final_checkpoint)]) =>
                SOME (flag,
                  w2n (lookup_storage 0w (lookup_account 0x1001w before.accounts).storage),
                  w2n (lookup_storage 0w (lookup_account 0x1001w after.accounts).storage),
                  resumed_context.pc, LENGTH resumed.contexts,
                  final_context.returnData,
                  w2n (lookup_storage 0w
                    (lookup_account 0x1001w checkpoint.accounts).storage))
            | _ => NONE)
        | _ => NONE)
    | _ => NONE
End

val () = cv_auto_trans reentry_summary_def;

Theorem bytecode_reentry_updates_resumed_world:
  reentry_summary = SOME (1w, 0, 7, 29, 1, [7w], 0)
Proof
  CONV_TAC cv_eval
QED
