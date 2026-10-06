# Interpreter architecture: EVM boundary review

Status: proposal for review, not an implementation commitment.

This note refines the external-interaction questions in [design.md](design.md).
It records inspected implementation evidence and identifies decisions to make
before expanding the Solidity interpreter. It does not specify all core syntax,
reference representations, or evaluation schedules yet.

## Evidence and revision scope

- Verifereum: project dependency in `.holbuild/src/verifereum`, revision
  `1b6508cefacfd54f78437fb72d7962503ddbe96c` (our pinned version).
- Vyper-HOL: local checkout `/home/ubuntu/vyper-hol`. The checkout changed HEAD
  during this inspection, from `bf32bb56c4e6afe4548a1fb5827ca9643b793ccc` to
  `7ce7a3a0bbf80abae20b1930744f49e0367b95da`; observations below describe the
  files read, not a verified immutable snapshot. Its `holproject.toml` pins a
  different Verifereum revision, `f5e172ccbf45addef7096feea76428de3ed3dfa8`.

Paths below are relative to the respective repositories. Definitions and theorem
statements were inspected; neither upstream development was rebuilt for this
review. Vyper-HOL is architectural evidence, not a dependency to copy unchanged.

## What Vyper-HOL demonstrates

### Direct execution through an EVM adapter

`semantics/vyperInterpreterScript.sml` defines `make_ext_call_state`,
`extract_call_result`, and `run_ext_call`.

The adapter creates a single EVM context, shares account and transient-storage
representations, performs value transfer, dispatches precompiles separately, and
otherwise invokes Verifereum's `run_call`. Success extracts accounts, transient
storage, return data, and logs. A revert restores the supplied original accounts
and transient storage and discards callee logs. Other exceptions become `NONE`.

This is evidence that a source interpreter can call the EVM definition directly
and use `cv_auto_trans`. It does **not** require a recursive source interpreter
for external targets. Reentry consequently follows deployed bytecode.

Important limitations for our design:

- It uses a default call gas limit of `2 ** 64`, not an exact source gas model.
- It initializes access sets and deletion tracking for this invocation; it does
  not preserve the entire transaction execution state through this interface.
- Its exceptional-result classification is not sufficient for Solidity
  low-level calls, where EVM exceptional failure must be representable as a
  failed call rather than simply an invalid semantic state.
- `semantics/vyperCreateScript.sml`'s `eval_create` installs constructed runtime
  code through account helpers. This is not a general arbitrary-initcode EVM
  creation handler to reuse for Solidity `new`.

### A direct interpreter can have a proved CPS implementation

`semantics/vyperStateScript.sml` defines a state-exception monad; state remains
available with exceptional outcomes. The external function wrapper in
`vyperInterpreterScript.sml` restores the input abstract machine on failure.

`semantics/vyperSmallStepScript.sml` defines explicit continuation datatypes,
CPS evaluation, `stepk`, and an `OWHILE` driver. Theorems
`eval_stmts_eq_cont_cps` and `eval_expr_eq_cont_cps` relate this implementation
to direct evaluation. This supports keeping a readable definitional semantics
while deriving a first-order execution engine.

However, Vyper's termination argument uses bounded loops and nonrecursive
internal calls. Solidity needs its own fuel discipline. These theorems are not
fuel-stability or external-interaction-tree theorems for Solidity.

## What our pinned Verifereum actually exposes

### State is richer than accounts plus storage

`spec/vfmContextScript.sml` defines:

- `rollback_state`: accounts, transient storage, access sets, pending deletions;
- `context`: EVM stack/memory/PC, return data, gas used, refund counters, logs,
  and message parameters;
- `execution_state`: a stack of contexts with checkpoints, transaction
  parameters, current rollback state, and domain enforcement/collection mode.

`get_original` in `spec/vfmExecutionScript.sml` reads accounts from the bottom
checkpoint. Original storage matters to EVM storage gas/refunds. A fresh
single-context execution cannot simply substitute current source-mutated
accounts for transaction-original accounts without changing that behavior.

### Call entry is not the same as running a callee

`step_call` performs opcode setup: gas calculation, memory expansion, warm
access tracking, delegated-code lookup, static restrictions, balance and depth
checks. `proceed_call` captures a checkpoint, transfers value, constructs the
appropriate call context, and dispatches precompiles.

`run_call` runs while execution remains at or below the starting frame, stopping
when that frame finishes or returns to its caller. It does **not** by itself do
CALL entry setup. `run_within_frame` instead stops when depth changes and is not
a replacement for completing nested calls.

`handle_exception` and `pop_and_incorporate_context` implement nested-frame
return, rollback, logs, gas refunds, and output copying. A single remaining
context takes a different exit path: the adapter must provide the corresponding
outer boundary policy rather than assume nested rollback already happened.

`step_create` and `proceed_create` cover CREATE/CREATE2 entry, address derivation,
nonce changes and checkpoints. `handle_create` handles runtime-code installation
and code-deposit constraints. `run_create` is a transaction-entry helper, not a
standalone source-level CREATE opcode API.

The execution functions return option-valued results through `OWHILE`. We must
retain the distinction between EVM failure and inability to obtain a valid
execution result. This review has not established the precise termination
hypotheses for every proposed adapter input.

## Additional context: Vyper-HOL issue #98

[Issue #98](https://github.com/verifereum/vyper-hol/issues/98) and its three
comments were read using `gh api` (the local `gh issue view` failed on a deprecated
GraphQL field). This is proposed design context, not implemented behavior.

The September 18 follow-up materially sharpens the architecture:

- Gas observations should be **distinguished-frame scoped**, not a destructively
  consumed flat transaction oracle. In A -> B -> A, the source interpreter for
  outer A delegates the entire nested subtree to the EVM; it must not consume
  observations belonging to B or reentrant A.
- The oracle is temporary ghost execution evidence, not persistent world state.
  Consumption does not roll back on revert. Entry supplies it and returns the
  unused suffix; exhaustion is explicit failure. Tests can require exact
  consumption without imposing that requirement on the general semantics.
- A simulation must justify observations against concrete compiled-frame GAS
  steps, excluding deeper contexts. Using the same arbitrary oracle on both
  sides is not by itself a correctness argument.
- Explicit gas expressions must remain in the AST and be evaluated normally.
  Gas observations for calls and creation need precise meanings: available,
  requested, capped, and actual callee gas are different quantities.

The final comment recommends compiler correctness at an **arbitrary fresh EVM
frame with caller contexts underneath**, using `run_call`, rather than only at a
closed transaction boundary. Both executions delegate nested bytecode subtrees
to the EVM. On this model, outer-frame correctness need not assume compiler
correctness of every nested contract or introduce recursive linking. Separate
frame-entry theorem applications could transfer source properties to nested
and reentrant invocations. This is a intended theorem shape, not an established
Solidity theorem or a completed Vyper-HOL compiler proof.

The comment also identifies a possible missing prefix / nested-frame run /
return-suffix decomposition theorem. We should inspect existing frame results
and establish the needed statement before requesting upstream work. In
particular, framing preservation alone is not execution decomposition.

For Solidity, reserve query-specific observation operations (`gasleft`, call
budget, creation budget) and a frame-local evidence channel separate from world
state and source fuel. An oracle is a promising alternative to a fixed budget,
not a complete solution for source out-of-gas behavior: absence of a GAS query
does not imply absence of gas-sensitive failure.

## Proposed direction

### 1. Direct execution through a fixed Verifereum adapter

Decision after review: the primary evaluator calls a named, fixed Verifereum
adapter and then continues. It is not parameterized by an arbitrary handler.
Keep source operand evaluation separate from EVM execution through a small
first-order request/response interface.

A request must distinguish CALL, STATICCALL, DELEGATECALL, CREATE, and CREATE2;
carry target/code-context information, bytes, value/salt where appropriate,
requested gas, and the calling frame's context. A response must distinguish
success, revert, exceptional EVM failure, and adapter/domain errors, with return
data and relevant execution-state changes. High-level ABI validation and
try/catch classification belong to source semantics after the EVM response.

Explicit suspension, arbitrary handler parameterization, and higher-order
interaction trees are not foundational requirements. Reconsider them only if a
concrete proof or execution requirement justifies the additional machinery.
A derived first-order continuation implementation remains possible, related to
the direct evaluator by a theorem, as demonstrated by Vyper-HOL.

### 2. Align with Vyper-HOL's intended frame-boundary architecture

Decision after review: follow the intended/final Vyper-HOL solution, currently
articulated in issue #98, rather than copying its current adapter limitations.
Recheck the landed design when that issue is completed; its present proposals
are our alignment target, not an already implemented upstream interface.

Define meaningful Solidity interpreter state, reusing Verifereum types wherever
appropriate, and an explicit correspondence relation to concrete EVM state.
Do not require artificial EVM stack/memory/PC values in source state or assume
that correspondence is a uniquely invertible projection. The intended compiler
boundary is an arbitrary distinguished invocation frame with caller contexts
underneath, delegating complete nested bytecode subtrees to Verifereum.

Original accounts, access sets, pending deletions, domain mode, transaction
parameters, checkpoints, logs and refunds each need a justified treatment in
this correspondence and the bytecode adapter. They need not all be fields of
source interpreter state: inspect the intended upstream solution to determine
what is represented, supplied at the boundary, or abstracted with an explicit
proof obligation. Do not independently commit to a full execution-state carrier
or a synthetic EVM parent frame before that investigation.

All source writes must be visible to the callee before execution, and all
successful callee changes must be visible to subsequent source reads, including
writes made by bytecode reentry into the source-interpreted account.

### 3. Delegate mechanisms, without claiming source gas fidelity

Prefer an adapter that reuses EVM entry and exit mechanisms over reproducing
value transfer, depth, rollback, static restrictions, precompiles, or creation.
A synthetic parent EVM context running the relevant opcode is one candidate,
not yet a recommendation: it needs careful PC/output/memory/checkpoint setup
and introduces adapter memory costs.

Exact gas correspondence remains unsolved because ordinary source operations
do not yet consume compiler-equivalent gas. Passing explicit call gas does not
solve EIP-150 capping, stipends, caller overhead, or `gasleft()`. Any provisional
budget policy must be named and must not claim gas-sensitive compiler agreement.

### 4. Keep frame completion separate from transaction finalization

Source-frame failure must undo successful nested effects as well as local
source writes. Fuel exhaustion and unsupported states are not EVM reverts and
must not yield a committed successful observation. Keep raw execution results
separate from committed frame observations.

Transaction finalization (fees, refund caps, deletion processing, transient
storage lifecycle) is another boundary. Do not run transaction finalization for
each source-level external call.

## Source fuel decision

Decision after review: use recursive-depth fuel, not a globally consumed step
budget. Recursive evaluator calls receive a smaller bound; sibling computations
reuse the available bound. Loops and recursive internal calls must decrease fuel.
Bytecode subtrees use Verifereum execution, independently of source fuel. Fuel
is used only as lightweight machinery where needed to establish termination in
HOL, not as a general execution-cost budget. Independently terminating helpers
use structural or well-founded recursion without fuel. Specify minimal sufficient
decrement points with the evaluator equations and prove terminal-result stability.
Fuel is not a measure of total source work.

## Runtime values and typing decision

Decision after review: follow Vyper-HOL's separation of simple runtime values
from source types. Scalar constructors retain value categories but do not carry
integer widths/signedness or bytes bounds. Typed core operations determine
arithmetic, conversions and cleanup; bindings retain declared types, and
references carry the location/type/layout descriptors needed for navigation.
Annotation validation and a separate runtime typing relation must justify the
core's type assumptions rather than relying on redundant tags in every value.

This follows the recorded decision in Vyper-HOL [#45](https://github.com/verifereum/vyper-hol/issues/45),
the scalar refactoring in [#175](https://github.com/verifereum/vyper-hol/pull/175),
and subsequent array refactoring in [#208](https://github.com/verifereum/vyper-hol/pull/208).
[#97](https://github.com/verifereum/vyper-hol/issues/97) additionally motivates
lazy storage access rather than eager aggregate materialization. These sources
were read along with current value, AST and scope definitions.

Solidity needs richer reference semantics than Vyper-HOL's tree-shaped aggregate
values and specialized top-level storage references: memory aliasing, calldata
views and locally captured storage references must fit the runtime model.
Their precise representation remains to be designed. The annotation issues in
[#308](https://github.com/verifereum/vyper-hol/issues/308) reinforce that frontend
and core validation require independent scrutiny.

## Reference binding and copying decision

Decision after review: elaboration explicitly distinguishes location navigation
and capture, local reference binding/rebinding, and content copying. Validation
checks the classification against source/destination types, locations and
binding kinds; the interpreter does not infer it from a generic assignment.

For admitted reference-type assignments:

- memory-to-memory local assignment aliases;
- storage-to-local-storage-reference assignment binds/rebinds a captured location;
- calldata-to-calldata local assignment preserves a read-only view;
- storage/calldata-to-memory assignment allocates and copies contents;
- assignment into a storage object copies contents, rather than rebinding it.

These are not blanket admissibility rules: mappings and other restricted types
need explicit restrictions. Scalar reads/assignments remain value operations.

Storage navigation is lazy, following Vyper-HOL's slot-backed `HashMapRef` and
`ArrayRef` precedent (`vyperStateScript.sml`: `evaluate_subscript`,
`toplevel_array_length`, and separate `materialise`). Solidity layout rules are
different and must not reuse Vyper slot formulas blindly. Binding, indexing,
and single-element reads must not enumerate huge static arrays. Whole-object
copying is a separate operation whose fuel/termination discipline still needs
design. Captured storage locations do not reevaluate an old index path or repeat
its bounds checks; new suffix navigation uses current storage.

Decision after review: core aggregate copying is a typed operation over source
and destination references, not mandatory eager materialization into an aggregate
value. This is important for execution in logic as well as huge storage arrays.
Copy helpers should navigate locations and update contents incrementally; exact
ordering and alias/overlap behavior still require specification. Concrete
reference datatypes and exact copy rules remain open.

Decision after review: copying has an independent termination proof and does not
consume source fuel. Use finite traversal bounds and well-founded type/layout
structure, with explicit well-formedness assumptions for recursive types and
copy restrictions. This is a proof obligation, not yet an established theorem.
Avoiding materialization addresses execution cost; logical totality alone does
not make a huge whole-object copy cheap.

### Pinned Solidity reconnaissance: assignment and copy helpers

Inspected through `gh api` at `SOLIDITY_PIN` (no compiler execution):

- `docs/types/reference-types.rst`, section "Data location and assignment
  behavior", confirms location-dependent copying and reference binding. Memory
  aliasing is not restricted to locals: in
  `libsolidity/codegen/ir/IRGeneratorForStatements.cpp`, `writeToLValue` stores a
  memory reference directly into a memory aggregate member when the RHS is
  already in memory. Core binding/replacement must therefore cover heap reference
  fields too, not only local variables.
- `libsolidity/codegen/YulUtilFunctions.cpp`, `copyArrayToStorageFunction`,
  reads length, resizes the destination, then copies elements in ascending order
  through typed recursive storage updates. `copyStructToStorageFunction` updates
  members in declaration order. Storage-source helpers guard exact same-base
  self-assignment rather than first materializing a whole source snapshot.
- `copyValueArrayToStorageFunction` uses packed-slot handling and conversions,
  destination resizing/cleanup, a same-base early return, and a resource-error
  length guard. These rules need representation in profile fidelity work; a
  generic immutable-tree assignment is not sufficient evidence of equivalence.
- Semantic fixtures under `test/libsolidity/semanticTests/array/copying/`,
  including `array_copy_storage_storage_struct.sol` and
  `array_copy_storage_storage_dynamic_dynamic.sol`, exercise copying and cleanup.
  Their recorded expected outputs were read, not rerun. They do not establish
  general overlapping-copy semantics.
- The documentation's "Dangling References to Storage Array Elements" section
  explicitly describes compiler behavior but labels dangling-reference programs
  undefined behavior. Captured-location execution must not be presented as a
  portable language guarantee for such programs.

Conclusion: do not assume universal snapshot/memmove semantics. The inspected
via-IR helpers interleave reads and writes; this alone does not establish an
observable difference on a valid ordinary program. General overlap, compiler
bugs, custom layouts and hash collisions need separate classification and
witnesses. Preserve the ability to specify ordered copying without eager
whole-object materialization; the exact canonical copy rules remain open.

## Evaluation schedule decision

Decision after review: elaboration fixes evaluation order explicitly, keeping
profile-dependent scheduling out of the interpreter. Ordered core operations
and temporary bindings distinguish expression evaluation, location capture and
writes/binding/copying. Short-circuiting uses explicit control flow. The
interpreter follows the elaborated schedule; normalization must preserve effects
throughout, including effects in lvalues and hoisted call operands.

The inspected pinned via-IR assignment lowering evaluates the RHS before the
LHS, and `writeToLValue` writes tuple components in reverse order. These are
construct-specific observations, not a complete schedule specification. Full
construct coverage and canonical/profile schedule differences still need
reconnaissance and validation tests.

## Control flow and modifiers: review findings

Inspected Vyper-HOL `vyperStateScript.sml` and `vyperInterpreterScript.sml`:
control flow uses exceptions (`ReturnException`, `BreakException`,
`ContinueException`) in a state-exception monad. `handle_function` catches return
and propagates runtime failure; `handle_loop_exception` catches break/continue
and propagates other outcomes. Internal calls save/restore scopes through
`finally`. This supports structured outcomes and boundary-specific handlers,
not rollback on every propagated outcome. Solidity cannot copy Vyper's
nonrecursive-call termination assumptions or its nonreentrant cleanup policy.

Inspected at `SOLIDITY_PIN` through `gh api`:

- `docs/contracts/function-modifiers.rst`: return exits the current body or
  modifier, allowing the enclosing modifier to continue after its placeholder;
  modifiers may skip the body or invoke it repeatedly.
- `libsolidity/codegen/ir/IRGenerator.cpp`, `generateModifier` and
  `generateFunctionWithModifierInner`: via-IR generates a chain of wrapper
  functions. Placeholders call the next wrapper/body and obtain its return
  values. Modifier arguments are evaluated on wrapper entry, rather than all
  being hoisted to original function entry. Parameter values are passed to the
  inner invocation, while reference values preserve the relevant aliases.
- `IRGeneratorForStatements.cpp`, `endVisit(Return)` emits return-variable
  assignments followed by Yul `leave`; `endVisit(PlaceholderStatement)` emits
  the next-wrapper call. Ordinary return is consequently local to that wrapper.
- `semanticTests/modifiers/return_does_not_skip_modifier.sol`: recorded return
  is 2 and modifier postlude writes state variable x to 9.
- `function_modifier_multi_invocation_viair.sol`: repeated body execution of
  `r += 1` returns 1 even when invoked twice. The corresponding legacy-only
  `function_modifier_multi_with_return.sol` records 2 for two invocations and
  explicitly notes fresh return variables in via-IR versus shared legacy slots.
  A single shared return/local environment across placeholders is therefore
  not a faithful implementation of our pinned via-IR profile.
- `return_in_modifier.sol` exercises modifier-local return from a loop;
  `function_modifier_multiple_times_local_vars.sol` exercises separate modifier
  locals. Recorded expectations were read, not executed in this review.

Decision after review: elaborate modifiers into resolved internal wrapper/body
procedures using the ordinary core invocation mechanism, not textual statement
insertion or a single global return handler. Each invocation has its own binding
scope; reference arguments still share locations according to the reference
rules. Model return bindings and their initialization/passing explicitly to
preserve via-IR repeated-placeholder behavior. Calls catch local return; loops
catch local break/continue. Revert/panic and semantic resource/error outcomes
propagate without executing modifier postludes. Source-frame commit/rollback
remains an external entry boundary operation, not an internal-call operation.

The wrapper-based architecture is agreed; detailed return-value wiring,
memory-reference returns, modifier argument reevaluation under repeated outer
placeholders, constructor wrappers, dispatch and canonical-versus-profile
behavior still need focused witnesses.
Generated wrappers are finite elaborated syntax; their introduction does not
justify adding fuel where structural termination suffices, though potentially
recursive source invocations still require the agreed fuel discipline.

## Decisions for review

1. Resolved: direct evaluation through a fixed Verifereum adapter is primary.
   Suspension or handler parameterization requires a concrete future justification.
2. Resolved direction: meaningful source state plus explicit EVM correspondence,
   aligned with the intended/final Vyper-HOL #98 solution. Concrete representation
   and adapter details remain pending investigation of that upstream design.
3. Should frame-local gas evidence be the intended abstraction, with a fixed
   budget only for explicitly restricted prototype tests? Which observations
   and out-of-gas outcomes must it cover for conformance claims?
4. How much adapter infrastructure should be proved before extending the core?

These are proposals, not changes to the canonical evaluation order or memory
model. The existing bytecode-reentry limitation remains explicit.

## Bounded derisking work

Before expanding language coverage:

1. Freeze an upstream revision for reproducible follow-up experiments.
2. Inspect Vyper-HOL's intended state correspondence and arbitrary-frame compiler
   boundary, tracking #98 to its landed solution. Define aligned request/response
   and source-state correspondence candidates in HOL.
3. Exercise actual pinned EVM calls for success, revert, exceptional halt,
   empty-code targets, precompiles, static violations, and delegate context.
4. Exercise CREATE/CREATE2 success, initcode revert, address collision, and
   creator nonce behavior on failure.
5. Test two calls in one transaction, source writes before a call, bytecode
   reentry, successful inner effects followed by outer revert, and transient
   storage. Include original-storage and access-state preservation checks.
6. Prototype direct fuel-bounded evaluation through the fixed adapter and
   `cv_compute` translation; prove a narrowly scoped stability result. Introduce
   explicit continuations only if needed for execution or proofs.
7. Test frame-local gas evidence across opaque nested calls and outer revert:
   nested frames do not consume it, revert does not restore consumed evidence,
   and source fuel remains independent. Inspect arbitrary-frame preservation
   and the execution decomposition needed for future compiler theorems.

Acceptance requires deterministic results, no lost transaction state, explicit
failure classification, and a documented ownership boundary. These experiments
can use hand-written core fragments and bytecode; new `solc` fixtures are not
required to start. They validate the architecture, not compiler correspondence.
