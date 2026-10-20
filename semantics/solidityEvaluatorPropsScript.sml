(* Fuel stability for the pure evaluator: a result that is not fuel-truncated
 * is unchanged by more fuel. The environment and state are universally
 * quantified, so the statements carry over unchanged once external answers are
 * supplied through them.
 *)
Theory solidityEvaluatorProps
Ancestors
  solidityEvaluator

Theorem eval_fuel_stable[local]:
  (∀n env ss st gas m.
     (eval_block n env ss st gas).completion ≠ FuelExhausted ∧ n ≤ m ⇒
     eval_block m env ss st gas = eval_block n env ss st gas) ∧
  (∀n env s st gas m.
     (eval_stmt n env s st gas).completion ≠ FuelExhausted ∧ n ≤ m ⇒
     eval_stmt m env s st gas = eval_stmt n env s st gas) ∧
  (∀n env prelude c bd st gas m.
     (eval_loop n env prelude c bd st gas).completion ≠ FuelExhausted ∧
     n ≤ m ⇒
     eval_loop m env prelude c bd st gas =
     eval_loop n env prelude c bd st gas) ∧
  (∀n env f args st gas m.
     (invoke_source n env f args st gas).completion ≠ FuelExhausted ∧
     n ≤ m ⇒
     invoke_source m env f args st gas = invoke_source n env f args st gas)
Proof
  ho_match_mp_tac eval_block_ind >> rpt strip_tac >>
  qpat_x_assum ‘_.completion ≠ FuelExhausted’ mp_tac >>
  once_rewrite_tac[eval_block_def] >>
  (* statements without nested evaluation, and the empty block *)
  TRY (strip_tac >> REFL_TAC >> NO_TAC)
  >~ [‘eval_stmt _ _ _ _ _’] >-
   (strip_tac >> first_x_assum (qspec_then ‘m’ assume_tac) >>
    rename1 ‘eval_stmt _ _ s _ _’ >>
    Cases_on ‘(eval_stmt n env s st gas).completion = NormalCompletion’ >>
    gvs[])
  >~ [‘bind_call_result’] >-
   (strip_tac >> Cases_on ‘eval_atoms st.scopes atoms’ >> gvs[] >>
    rename1 ‘invoke_source _ _ f vs _ _’ >>
    Cases_on ‘(invoke_source n env f vs st gas).completion = FuelExhausted’ >>
    gvs[bind_call_result_def])
  >~ [‘loop_after_body’] >-
   (qpat_x_assum
      ‘∀m. (eval_block n env prelude _ _).completion ≠ _ ∧ _ ⇒ _’
      (qspec_then ‘m’ mp_tac) >>
    qabbrev_tac ‘r1 = eval_block n env prelude (push_scope st) gas’ >>
    Cases_on ‘r1.completion = FuelExhausted’
    >- gvs[LET_THM, pop_result_def] >>
    simp[] >> disch_then (fn th => simp[th, LET_THM]) >>
    Cases_on ‘r1.completion = NormalCompletion’ >> gvs[] >>
    Cases_on ‘branch_of r1.state c’ >> gvs[] >>
    rename1 ‘SOME b’ >> Cases_on ‘b’ >> gvs[] >>
    qabbrev_tac
      ‘r2 = eval_block n env bd r1.state r1.unused_gas_evidence’ >>
    Cases_on ‘r2.completion = FuelExhausted’
    >- gvs[pop_result_def, loop_after_body_def] >>
    gvs[] >>
    Cases_on ‘loop_after_body (pop_result r2).completion’ >> gvs[] >>
    Cases_on ‘n = 0’ >> gvs[])
  >~ [‘lookup_procedure’] >-
   (strip_tac >> Cases_on ‘n = 0’ >- gvs[abrupt_result_def] >>
    ‘m ≠ 0’ by decide_tac >> simp[] >>
    rename1 ‘lookup_procedure env f’ >>
    Cases_on ‘lookup_procedure env f’ >> gvs[] >>
    rename1 ‘lookup_procedure _ _ = SOME p’ >>
    Cases_on ‘entry_scope env p args’ >> gvs[] >>
    rename1 ‘entry_scope _ _ _ = SOME scope’ >>
    Cases_on ‘(eval_block (n - 1) env p.body (enter_procedure st scope)
                 gas).completion = FuelExhausted’ >>
    gvs[LET_THM, procedure_completion_def, abrupt_result_def])
  >~ [‘branch_of’] >-
   (strip_tac >> Cases_on ‘branch_of st c’ >> gvs[] >>
    rename1 ‘SOME b’ >> Cases_on ‘b’ >> gvs[pop_result_def])
  (* while statement *)
  >> strip_tac >> gvs[]
QED

Theorem eval_block_fuel_stable:
  eval_block n env ss st gas = r ∧ r.completion ≠ FuelExhausted ∧ n ≤ m ⇒
  eval_block m env ss st gas = r
Proof
  metis_tac[eval_fuel_stable]
QED

Theorem invoke_source_fuel_stable:
  invoke_source n env f args st gas = r ∧ r.completion ≠ FuelExhausted ∧
  n ≤ m ⇒
  invoke_source m env f args st gas = r
Proof
  metis_tac[eval_fuel_stable]
QED
