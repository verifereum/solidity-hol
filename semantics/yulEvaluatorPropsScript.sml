(* Fuel stability for the Yul evaluator: a run that does not run out of fuel
 * is unchanged by more fuel.
 *
 * Fuel is only ever tested for zero, and is spent only where the recursion is
 * not structural -- a loop's back edge and a call's entry -- so a larger bound
 * can neither turn a real answer into out-of-fuel nor change one: it can only
 * replace YulOutOfFuel by the answer the run would have reached.
 *
 * Expressions return a yul_expr_result rather than a yul_result, so the "did
 * not stop for fuel" side condition is yul_running instead of a completion
 * test.  The conjuncts are in the definition's order: block, stmt, expr, args,
 * loop, cases, call.
 *)
Theory yulEvaluatorProps
Ancestors
  yulEvaluator

Definition yul_running_def:
  (yul_running (EvalValues vs m) ⇔ T) ∧
  (yul_running (EvalAbrupt c m) ⇔ c ≠ YulOutOfFuel)
End

Theorem eval_yul_fuel_stable[local]:
  (∀n fns ss m k.
     (eval_yul_block n fns ss m).completion ≠ YulOutOfFuel ∧ n ≤ k ⇒
     eval_yul_block k fns ss m = eval_yul_block n fns ss m) ∧
  (∀n fns s m k.
     (eval_yul_stmt n fns s m).completion ≠ YulOutOfFuel ∧ n ≤ k ⇒
     eval_yul_stmt k fns s m = eval_yul_stmt n fns s m) ∧
  (∀n fns e m k.
     yul_running (eval_yul_expr n fns e m) ∧ n ≤ k ⇒
     eval_yul_expr k fns e m = eval_yul_expr n fns e m) ∧
  (∀n fns es m k.
     yul_running (eval_yul_args n fns es m) ∧ n ≤ k ⇒
     eval_yul_args k fns es m = eval_yul_args n fns es m) ∧
  (∀n fns cond post body m k.
     (eval_yul_loop n fns cond post body m).completion ≠ YulOutOfFuel ∧
     n ≤ k ⇒
     eval_yul_loop k fns cond post body m =
     eval_yul_loop n fns cond post body m) ∧
  (∀n fns v cases default m k.
     (eval_yul_cases n fns v cases default m).completion ≠ YulOutOfFuel ∧
     n ≤ k ⇒
     eval_yul_cases k fns v cases default m =
     eval_yul_cases n fns v cases default m) ∧
  (∀n fns name args m k.
     yul_running (invoke_yul n fns name args m) ∧ n ≤ k ⇒
     invoke_yul k fns name args m = invoke_yul n fns name args m)
Proof
  cheat
QED

Theorem run_yul_fuel_stable:
  run_yul n code m = r ∧ r.completion ≠ YulOutOfFuel ∧ n ≤ k ⇒
  run_yul k code m = r
Proof
  rw[run_yul_def] >> metis_tac[eval_yul_fuel_stable]
QED
