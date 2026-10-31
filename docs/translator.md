# Core-to-HOL translator

## Overview

Proofs about a Solidity program should be about ordinary HOL functions, not
about runs of the evaluator. The semantics of a program is its elaborated core
program (`elaborate_unit`, `semantics/solidityElaborateScript.sml`) run by the
fuel-indexed core evaluator (`semantics/solidityEvaluatorScript.sml`); there is
no second, closer-to-source semantics. Reasoning about the evaluator directly
means unfolding fuel, scopes, capture targets and the elaborator's
administrative temporaries in every proof.

The translator (`translator/solidityTranslateLib`) removes that layer once per
program. For each function of a unit it defines a *shallow function*: a HOL
function over native values whose body reads like the source. It then proves
that the evaluator computes it. Users prove properties of the shallow
functions, and the correspondence theorem carries them to the evaluator.

## Shallow functions

A shallow function takes its parameters as HOL values (`uintN` as `num`,
`bool` as `bool`) and returns a `sol_result` (`translator/solidityShallowScript.sml`):
`Returns v`, `Reverts bytes` or `Panics code`. Several results are a tuple.
`sol_bind` sequences two computations and propagates `Reverts` and `Panics`;
the checked operations (`uint_add`, `uint_sub`, `uint_mul`, `uint_div`,
`uint_mod`) panic with the Solidity panic codes on overflow and division by
zero.

`fact` from `testdata/frontend/pure_core.sol` comes out as

```
fact n = if n = 0 then Returns 1
         else sol_bind (fact (n - 1)) (λr. uint_mul 256 n r)
```

The subtraction `n - 1` is plain arithmetic: on that path `n ≠ 0`, so the
translator drops the underflow check that can never fail. Only operations whose
check the path condition does not decide become binds.

A loop becomes a helper function, `f_loop`, over the variables the loop uses.
`break` returns the current values, `continue` and falling through make the
recursive call. All shallow functions are total HOL definitions, so users get
equations and an induction principle.

## Correspondence theorems

For a function `f` with procedure id `i` the translator proves `f_correct`:

```
⊢ ∀n. n < 2 ** 256 ⇒
      (∀res. fact n = Returns res ⇒ res < 2 ** 256) ∧
      ∃N. ∀m st gas. N ≤ m ⇒
        invoke_source m env (AstId i) [uint_value n] st gas =
        <|completion := result_completion (λres. [uint_value res]) (fact n);
          state := st; unused_gas_evidence := gas|>
```

- The only hypotheses are that the arguments are in range for their types.
  The first conjunct says the results are in range too, which is what a
  caller's theorem needs.
- Fuel is existential: some fuel `N` suffices, and so does any larger amount.
  The shallow function has no fuel, so `FuelExhausted` never appears.
- `result_completion` maps `Returns`, `Reverts` and `Panics` back to the
  evaluator's return, revert and panic completions. Return, break and
  continue inside the body are control flow in the shallow term, not results.
- The state is unchanged, since the covered fragment has no storage.

`env` is `core_program_environment prog` for the program `prog` with
`elaborate_unit src = SOME prog`, so chaining with that theorem gives a
statement about the source unit.

A loop helper's theorem `f_loop_correct` is about `eval_loop` from any state
whose scopes give the loop's variables their values, and says what the scopes
hold afterwards. It does not depend on where the loop sits.

## How a function is translated

**Generation.** The translator symbolically executes the procedure body in ML
over a map from declaration ids to HOL terms. Temporaries, capture targets and
copies only update the map, so they never become names in the output. When both
branches of an `if` fall through and neither can fail, each changed variable
becomes a conditional. Checked/calling branches whose successful paths all
continue return the changed outer bindings; one `sol_bind` receives those values
and translates the remaining block once. Failures propagate through that bind.
Source `return`, `break` and `continue` retain their separate exits. The elaborator's first-iteration flag of `for` and `do`-`while` loops
is removed by peeling the first iteration, after which the flag is constant.

**Proof.** The proof is an induction along the shallow function's definition
(when it is recursive) and a case split along its control flow. At each call of
a callee, a loop helper or the function itself, it uses that function's theorem
or the induction hypothesis; the rest is rewriting the evaluator on the
concrete body, with one lemma per core operation in `solidityShallow`.

## Evaluator interface

`solidityEvaluatorProps` owns the compositional equations `eval_block_cons`,
`eval_loop_unfold`, `invoke_source_unfold` and `result_literal_eqs`, with their
concrete helpers `block_next`, `call_finish`, `loop_prelude` and `loop_body`.
The translator consumes these maintained equations. Intermediate results remain
named until they are record literals, so rewriting does not duplicate an
unevaluated statement or call. These equations have no runtime-state/frame
preconditions; invalid execution, abrupt completion and fuel exhaustion retain
the evaluator's behavior.

Procedure correspondence requires in-range arguments, but permits any incoming
runtime state, including a static frame: the translated local-only fragment
leaves the world unchanged. Loop correspondence additionally records the bindings
for live inputs, existing outputs and constant flags, and the updated scopes and
targets. These statements do not give progress for arbitrary well-formed core.
Storage translation will need an effect/frame contract; static-frame storage
writes are invalid today.

## Using it

```
translate_unit {prefix, unit_def, program_def, termination, loops}
```

takes HOL definitions naming an imported source unit and its elaborated
program. For artifact input, first use `solidityPrepareLib` to check the pinned
artifact contract, source validity and complete core well-formedness. Its result
provides unit/program terms and certificates; define constants for those terms
and pass their definition theorems here. Raw import/elaboration helpers retain
these checks as caller preconditions. It defines
`prefix ^ "env"` and, callees first, every function `prefix ^ f` with its
theorem. `termination` and `loops` give, by function name, a termination
tactic for a recursive function or a loop helper when HOL cannot find one.

It returns one result per function. A construct the translator does not
cover makes that function, and its callers, `Unsupported` with a message
starting `unsupported:`; any other failure is `Failed`, a translator bug.

## Corpus test

`tests/solidityTranslatorCorpusScript.sml` runs the translator on every
function of every suite of the differential corpus
(`testdata/differential/corpus.json`) and prints one `translator-result` line
per function. The build fails if a function fails other than as
`Unsupported`, or if its proof takes longer than the test's cap. It is part of
the `solidityHol` roll-up, so CI runs it.

## Not covered yet

- signed integers, addresses, fixed-size bytes, unchecked arithmetic, bit
  operations and conversions between types
- mutually recursive functions
- `return` inside a loop, nested loops, and more than one loop per function
- loops whose termination HOL cannot prove without a tactic
- storage, and external calls

## Branch-growth measurement

`tools/translator_growth.sml` constructs a checked core fixture with successive
branches updating one `uint8` local, through either checked addition or calls to
a checked-addition callee. Source metadata supplies names for this synthetic
fixture; the benchmark makes no source-elaboration claim.

```sh
TRANSLATOR_GROWTH_N=2 TRANSLATOR_GROWTH_MODE=calling \
  holbuild -j1 run tools/translator_growth.sml
```

It reports generated main-definition nodes, elapsed translation/proof time,
kernel primitive-inference count and new axiom count. The measured interval
includes translation of the unit and its common callee; HOL startup and the
core well-formedness check are outside it. The comparison uses clean worktrees
with the same proof engine and fixture; only branch joining differs. Repeated
measurements and their limitations are recorded alongside this document.

Memory and inline assembly, and the source-visible external-call context/gas
contract, remain unresolved design work beyond this consolidation.
