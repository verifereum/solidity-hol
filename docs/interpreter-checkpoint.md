# First executable ordered-core interpreter

Status: executable interpreter checkpoint over **hand-written core programs**.
This is not yet an admitted Solidity subset, an AST importer, or compiler
correspondence. The architecture decisions in [interpreter-design.md](interpreter-design.md)
remain authoritative. The previous [implementation blueprint](implementation-blueprint.md)
records the core/state and concrete EVM boundary work on which this builds.

## Entry points and implementation

- `semantics/solidityValueScript.sml`: binding/operand lookup, runtime shape
  checks, scalar arithmetic/conversion, captured writes and preseeded memory-cell
  helpers. These helpers terminate independently of source fuel.
- `semantics/solidityInterpreterScript.sml`: direct recursive ordered-core
  evaluation, lexical scope cleanup, internal invocation, loops and entry.
- `tests/solidityInterpreterTestScript.sml`: executable HOL regression proofs.

```text
eval_block    : num -> core_program -> core_stmt list
                   -> source_state -> gas_observation list -> source_result
invoke_source : num -> core_program -> ast_id -> runtime_value list
                   -> source_state -> gas_observation list -> source_result
run_source    : num -> core_program -> runtime_value list
                   -> source_state -> gas_observation list -> source_result
```

`run_source` invokes `program.entry_procedure`; the explicit invocation entry
can select any resolved procedure. No argument decoding or dispatch is provided.
All return **raw** source results. `finish_source_frame` remains a separate frame
observation policy, so resource exhaustion/invalid input cannot be mistaken for
committed success. There is no per-internal-call world rollback.

`eval_core` uses a first-order task tag to combine mutually dependent evaluator
clauses. It is direct execution, not a suspended interaction interface or a
continuation machine. `RunOperation` uses `ReturnCompletion [value]` as its
internal value-result convention; `DefineStmt` consumes that result. An internal
call produces a `TupleValue` containing its procedure returns, including the
zero-return case. Ordinary statement return is instead caught at invocation.

Definitions are translated to HOL's `cv_compute` representation with a proved
unconditional precondition. The CV execution has its own lexicographic
termination proof; it does not add fuel checks or change the source equations.
No cheats or new axioms are used.

## Fuel contract

Fuel is recursive-depth machinery, not a source-step or gas budget:

- Empty blocks, finite sibling statements, pure operations, if branches and
  scope cleanup do not decrement it. Finite pure blocks can run at zero.
- An internal invocation needs a positive bound and runs its body with one less.
  This handles potentially recursive procedure graphs. Sibling invocations reuse
  their caller's bound, including repeated modifier placeholders.
- A loop evaluates its condition prelude and body with its current bound.
  **Only taking the recursive back-edge** after normal/continue completion needs
  a positive bound and decreases it. False conditions, break, return and failures
  need no loop decrement. In particular, a breaking/returning body runs at zero.
- At exhaustion the raw state contains effects already performed. No successful
  committed frame observation is supplied by the resource outcome.

The termination measure is lexicographic in fuel and task/syntax size. Structural
recursion handles finite syntax; entering a procedure body and repeating a loop
are the fuel-decreasing edges. Runtime tuple checking uses a structurally
terminating worklist, not a hidden fuel budget.

Theorems establish pure-operation fuel independence and unconditional caller
binding/target restoration on invocation exit. Regression witnesses also compare
recursive runs at sufficient and excessive fuel. **A general terminal-result
fuel-stability theorem is not established yet.** It remains a next proof gate,
not a property inferred from the finite witnesses.

## Control, scopes and modifier wiring

Procedure invocation creates fresh parameter and return-binding scopes and a
fresh captured-target map. Supported scalar return bindings initialize to their
typed defaults. Normal fallthrough and `ReturnStmt []` read the named return
bindings; nonempty return operands provide explicit return values. Arity/type
checks reject mismatches. Return is local to the invocation.

Parameters are copied as runtime values, so reference parameters retain captured
location identity. On every invocation exit, the caller's scopes and target map
are restored; the returned world/heap remain those of execution. Callee locals
cannot see or mutate caller bindings by name. Break/continue escaping a procedure
become invalid outcomes rather than crossing the call boundary.

If branches and loop bodies have fresh lexical scopes. Each condition prelude
has a fresh iteration scope that remains available to its condition/body and is
removed before repetition or exit. Cleanup pops the executed scope rather than
restoring a saved copy of all scopes: writes to enclosing bindings survive.
Captured targets created inside these scopes do not leak out.

Modifier wrappers use ordinary internal calls and explicit tuple projections /
return-binding writes. The regression invokes a body twice with fresh return
bindings and then runs a postlude: each body returns 1, and the wrapper returns 2,
not 3 from accidentally sharing the body's return binding. Revert and panic from
the body skip the wrapper postlude. These are core wiring witnesses, not actual
compiler-generated modifier imports.

## Scalar and reference mechanics

Supported scalar operations include typed checked/unchecked integer addition,
subtraction, multiplication, division and remainder; equality and integer less
than. Widths/sign come from the operation type, not integer payloads. Overflow is
panic `0x11`; division by zero is panic `0x12`, including unchecked arithmetic.
Signed division truncates towards zero rather than using HOL's floor division;
remainder follows the dividend sign. Explicit integer conversions truncate to
the destination width. Other conversions/bitwise operations are not implemented.
Comparison operation annotations describe the **operand** type; their result
binding is boolean and is checked separately.

Capture, scalar write and reference rebinding are distinct operations. Bindings
retain declared type and assignability; writes do not infer content copying.
The reference witness captures memory location A, then rebinds its local to B:
the old captured target still identifies A and heap contents are not copied.
The fixture supplies heap objects and references directly; no allocator or
navigation rule is implied.

`read_memory` / `write_memory` provide sparse preseeded-cell mechanics with
bounds and actual-type checks. They do **not** establish root-object/field layout
validity or a source memory representation theorem. Reference binding checks
location/type descriptors, not an entire heap or storage layout. These helpers
are not a substitute for the pending reference environment and validity relation.
Do not admit arbitrary manufactured references as validated Solidity programs.

## Explicit limitations

The executable function is total on core input, but totality is not validation:

- There is no whole-core well-formedness checker or validated environment yet.
  Runtime checks cover bindings, return shape, missing/duplicate procedure IDs,
  scalar operands and several malformed operations; not every invalid annotation
  is rejected. No supported Solidity subset is claimed.
- Navigation, reference-field capture, allocation and content copying are
  unsupported, as are storage/transient/calldata scalar access rules. These need
  reviewed layout/type environments and independent copy termination.
- Reference-valued return defaults are unsupported. Their initialization and
  allocation require specification before such procedures can be admitted.
- External calls are explicit invalid/unsupported outcomes, not mock success,
  arbitrary handlers, or source-recursive execution. The named EVM adapter exists
  separately; source concrete-context supply still awaits the aligned #98 design.
- Frame-local gas observations are retained untouched. No gas query, consumption,
  source out-of-gas correspondence or gas-sensitive compiler claim is provided.
- ABI, constructors, modifiers' frontend elaboration, dispatch, automatic memory
  allocation, frontend import and transaction finalization remain future work.

## Validation and next work

```sh
holbuild build solidityHolTheory
python3 -B -m unittest discover -s tests -p 'test_*.py' -v
git diff --check
```

The HOL witnesses cover finite execution at zero fuel; condition repetition,
continue, break and return; exhaustion; checked/unchecked arithmetic and signed
rounding; explicit conversion; nested/repeated modifier-body invocation;
recursive scope isolation and depth; propagated revert/panic; named defaults;
invalid tuple projection, missing conditions and duplicate procedures; explicit
external-call rejection; and captured reference identity across rebinding.

Next: prove general terminal-result fuel stability and scope/typing invariants;
review the core typing for reference temporaries and return initialization; then
implement reference navigation and typed writes against a validated layout/heap
contract. External adapter integration must not silently settle context/gas
choices. Expanding standalone EVM fixtures is not the interpreter's next goal.
