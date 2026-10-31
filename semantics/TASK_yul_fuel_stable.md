# TASK: Fuel stability for the Yul evaluator

## Meta
Status: planned
Priority: P1
Created: 2026-10-31
Location: semantics/

## Theorem Statement (FROZEN)

`semantics/yulEvaluatorPropsScript.sml` (which builds today with a `cheat`)
holds the definition below and the theorem.  This is the exact text of the
file:

```sml
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
```

The same file also holds this public corollary, which is part of the task
(it follows from the theorem above):

```sml
Theorem run_yul_fuel_stable:
  run_yul n code m = r ∧ r.completion ≠ YulOutOfFuel ∧ n ≤ k ⇒
  run_yul k code m = r
Proof
  rw[run_yul_def] >> metis_tac[eval_yul_fuel_stable]
QED
```

The seven functions are the mutual definition `eval_yul_block_def` in
`semantics/yulEvaluatorScript.sml`, declared in the order block, stmt, expr,
args, loop, cases, invoke, which is the order of the seven conjuncts.  Its
induction principle is `eval_yul_block_ind`.

**Do not modify these statements.**  Prove them as-is, or produce a
counterexample.  In particular, do not change the definitions in
`semantics/yulEvaluatorScript.sml` or `syntax/yulASTScript.sml`; extra helper
lemmas and definitions in `semantics/yulEvaluatorPropsScript.sml` (or a new
theory) are fine.

(*
 ************************************************************
 * DO NOT START THIS PROOF until you have finished and
 * validated ALL the machinery you will need for it.
 * Especially machinery that can be generalized and shared
 * between proofs -- write it in separate helper files
 * (e.g. yulEvaluatorPropsScript.sml, yulEvaluatorLib.sml) and
 * build them first.
 *
 * Building generic, powerful abstractions (lemmas, tactics)
 * that help this proof IS explicitly in scope.
 ************************************************************
 *)

## Completion Criteria

1. `holbuild -j4 build yulEvaluatorPropsTheory` passes with zero CHEAT
   warnings and zero FAILs, and the final state of the file has no `cheat`
   anywhere (neither `Proof cheat QED` nor a `cheat` inside a tactic).
2. The two statements above are unchanged, byte for byte, apart from the
   proofs.
3. The proof uses no `TRY` or `ORELSE` around `metis_tac` or any other search
   tactic, and no tactic step of the final script may run over holbuild's
   default 2.5 s per-step tactic timeout; the timeout must not be raised, not
   in `holproject.toml` and not on the command line.
4. No new axioms, no `mk_thm`, no new `Definition` that changes what the
   evaluator means.  Any helper definition you add must be flagged in your
   report as a new definition.
5. No duplicate or near-duplicate lemmas: each helper exists once, in its most
   general form.

**If a statement is false as stated:**
- Produce a HOL4 counterexample (e.g. `EVAL_TAC` on concrete values).
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

From the root of this worktree (the directory holding `holproject.toml`):

```
holbuild -j4 build yulEvaluatorPropsTheory
```

The whole project's root target is `solidityHolTheory`, which must still build
afterwards (`holbuild -j4 build solidityHolTheory`); `yulEvaluatorProps` is
already in its `Ancestors`.

## Background

`solidity-hol` is getting a Yul semantics, for the middle layer of the
Solidity compiler-correctness chain (source -> Yul -> EVM).  The evaluator is a
fuel-indexed interpreter: every function takes a natural number `n` as its
first argument and recursion that is not structural is bounded by it, so the
interpreter always terminates and returns `YulOutOfFuel` instead of looping.

Fuel stability is the theorem that makes fuel usable: a run that does NOT end
in `YulOutOfFuel` at fuel `n` gives exactly the same result at any larger fuel
`k`.  It says fuel is only a bound on how far a run may go, never an input that
can change an answer, so a caller can pick a generous fuel, and a later proof
about the interpreter can replace `YulOutOfFuel` by "the run needed more".

The fuel is spent in exactly two places -- a loop's back edge and entering a
call -- and is tested for zero in `eval_yul_expr` (the `YulApply` equation) and
`invoke_yul`.  Everything else, including sibling statements in a block and the
arguments of one call, runs at the same bound.

## Domain Constraints

- HOL4 with holbuild only: `holbuild build <Theory>`, never Holmake.
- No `cheat` in what you call done.  If you need a temporary one while
  working, keep the original proof commented out above it.
- Never edit a proven statement in place; add a wrapper theorem and prove the
  two equivalent instead.
- Weaken assumptions, never strengthen them.  A new hypothesis is a change to
  a statement and is not allowed here.
- Never raise the tactic timeout (2.5 s default per proof step).  A step that
  runs over is a performance bug: split the step or cut its rewrite set.
- No `TRY` or `ORELSE` around `metis_tac`, `simp` or any other search: `TRY`
  catches the timeout exception, so such a step can pass locally and hang in
  CI.  Select goals with `>~`, `>-` and `>|` instead.
- Use `rename1`; never depend on generated names like `h''`.
- Write theories with `Theorem ... Proof ... QED` under
  `Theory`/`Ancestors`/`Libs` headers.
- Prefer `simp[Once def]` to `fs[recursive_def]`, `irule` to `metis_tac`, and
  keep each case short: a case that needs more than about three tactics gets
  its own lemma.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| The evaluator and its definition | `semantics/yulEvaluatorScript.sml` | `eval_yul_block_def` (the seven mutually recursive functions), `run_yul_def`, `eval_yul_builtin_def`, the `Termination` blocks and the cv translations |
| The existing Solidity evaluator's fuel-stability proof | `semantics/solidityEvaluatorPropsScript.sml` | the closest analogue: the same statement shape for a four-function mutual definition, proved by `ho_match_mp_tac eval_block_ind`, `qpat_x_assum '_.completion ≠ FuelExhausted' mp_tac`, `once_rewrite_tac[eval_block_def]`, then `>~` per recursive call |
| The Solidity evaluator's definition, for comparison | `semantics/solidityEvaluatorScript.sml` | the same fuel discipline |
| Result types, completion, machine | `semantics/yulStateScript.sml` | `yul_result`, `yul_completion` (`YulNormal`, `YulReturn`, `YulRevert`, `YulInvalid`, `YulOutOfFuel`, `YulBreak`, `YulContinue`, `YulLeave`), `yul_machine` |
| The AST | `syntax/yulASTScript.sml` | `yul_stmt`, `yul_expr`, `yul_literal`, `yul_function`, `yul_env`, and the size lemmas `yul_expr_size_pos` |
| The dialect | `semantics/yulDialectScript.sml` | builtin names and effect classes |
| Smoke tests | `tests/yulEvaluatorTestScript.sml` | `cv_eval` runs of small programs, including a fuel-exhaustion case |
| Build configuration and CI | `holproject.toml`, `.github/workflows/` | the targets CI builds |
| HOL libraries | the toolchain's `src` | `listTheory` (`list_size_def`), `basicSizeTheory` (`pair_size_def`), `pairTheory`, `cv_transLib`, `wordsLib` |

## Notes

- The statement's conjunct order must stay as it is: `ho_match_mp_tac
  eval_yul_block_ind` matches the induction principle's seven parts, which the
  definition generates in declaration order.
- The side condition is a completion test for the four functions that return a
  `yul_result` (block, stmt, loop, cases), and `yul_running` for the three that
  return a `yul_expr_result` (expr, args, invoke), where `EvalValues` is always
  running and `EvalAbrupt c` is running iff `c ≠ YulOutOfFuel`.
- The loop's out-of-fuel return keeps the machine it has reached and pops the
  scope the loop pushed (`yul_abrupt YulOutOfFuel (yul_pop_scope rp.machine)`),
  so a case analysis on a nested result must carry that machine through rather
  than discard it.
- `eval_yul_args` evaluates the tail of the argument list before its head and
  never tests the fuel; `eval_yul_cases` recurses down the case list at the
  same fuel.
- A program that never leaves a loop is the interesting case: at fuel `n` it
  returns `YulOutOfFuel`, so the theorem says nothing about it, which is
  exactly why the side condition is there.
