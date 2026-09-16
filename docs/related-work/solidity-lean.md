# SolidCore (`paradigmxyz/solidity-lean`)

Reviewed revision: `2cfd060ad1b3de35263f343a709988a5d8be1d63`.

Repository: <https://github.com/paradigmxyz/solidity-lean>

## Claim and scope

SolidCore is an executable Lean 4 semantics targeting Solidity 0.8.35. It
imports real compiler AST, typechecks and lowers it, executes a single-contract
source model, and differentially compares selected observable behavior with
pinned `solc` and Foundry/EVM execution.

The current contest scope is deliberately restricted. In particular, general
multi-contract execution, inline assembly, and exact gas introspection are not
part of the faithfully compared v1 subset. The implementation nevertheless has
an open-world interaction interface for calls and creation, driven in tests by
scripted responders.

Documentation in this rapidly evolving repository is not completely
synchronized: counts and proof descriptions differ between the top-level
README, `ARCHITECTURE.md`, and historical design notes. Exact quantitative
claims should therefore be taken from a pinned revision and reproduced rather
than combined across documents.

## Architecture

The implementation has four important representations or stages:

1. `Ast.lean` defines a broad surface Solidity AST.
2. `TypeCheck.lean` implements compiler-acceptedness checks.
3. `Interface.lean` resolves and lowers surface programs to executable core
   expressions and statements.
4. `Interpreter.lean` defines runtime values, state, ABI-facing behavior, and
   the fuel-indexed interpreter.

This separation is valuable, but the large lowering and interpreter modules
also illustrate the cost of broad source coverage. At the reviewed revision,
`Interface.lean` is about 30,000 lines, `TypeCheck.lean` about 16,000, and
`Interpreter.lean` about 11,000. Numerous historical divergences arose because
parallel lowering paths handled the same semantic issue differently.

## State and interaction

Runtime storage is a concrete word-keyed map and is converted to and from the
shared EVM world representation at the interaction boundary. Storage layout,
packing, dynamic arrays, mappings, and typed cleanup are source-semantics
responsibilities.

Memory is abstract rather than compiler byte-addressed. This matches
Solidity-HOL's tentative division between concrete storage and an alias-aware
source heap.

External behavior uses a free interaction monad. A request contains an
open-world snapshot; a response contains a post-world which the source runtime
adopts. The proved round-trip law says that snapshotting an adopted world
recovers the supplied world. This is a useful model for arbitrary environment
changes, including changes a reentrant execution could make, without embedding
a closed-world protocol runner in the Solidity semantics.

The corpus uses fail-closed scripted responders. An unanticipated request is
distinguished from an anticipated failed call.

## Fuel

Statement execution is fuel-indexed. Expression evaluation uses separate
syntax-derived structural bounds, so source fuel primarily controls statement
loops and internal recursion.

`FuelMonotonicity.lean` proves a strong interaction-tree stability property:
when a low-fuel tree has no reachable `outOfFuel` leaf for any sequence of
external answers, any greater fuel produces exactly the same interaction tree.
This is stronger than equality under one test responder and is relevant to
future composition with an external semantics.

This suggests that Solidity-HOL should decide early whether its public result is
a plain state result or an interaction computation. The strongest appropriate
fuel theorem depends on that choice.

## Evaluation order

SolidCore originally threaded a global child-order parameter. It later removed
that mechanism and made ordering intrinsic to constructs, based on the pinned
legacy code generator. Examples include:

- ordinary binary operands: right before left;
- ordinary argument and tuple lists: left to right;
- assignment: right-hand side before resolving the target;
- nested index base before key;
- Boolean short-circuiting: guarded left-first execution; and
- events: indexed arguments in reverse order followed by non-indexed arguments
  in forward order.

A particularly important discovery was that interpreter rules did not determine
order once calls had been hoisted out of expressions: importer/lowering prefixes
could execute calls in a different order before the residual expression reached
the interpreter.

This supports Solidity-HOL's plan to use deterministic elaborated syntax, but
argues against describing the canonical order merely as a uniform
left-to-right policy. At minimum, the language-canonical profile and each
compiler profile need a construct-by-construct order table, and elaboration
must preserve it through call normalization.

## Storage references

SolidCore changed indexed storage references from a root name plus an index path
to a captured concrete slot plus layout. This matches `solc` behavior:

```solidity
S storage p = arr[i];
arr.pop();
return p.a;
```

The bounds check and location calculation happen when `p` is bound. Later use
loads the captured slot; it must not recompute the old array path and repeat the
bounds check. Further indexing through `p` still uses current storage and
performs checks for the new suffix.

This is a direct design requirement for Solidity-HOL. A storage-reference value
should identify a concrete account, slot/byte offset, and layout/type needed for
subsequent navigation. Retaining both a symbolic path and captured slot as
competing authorities should be avoided.

## Differential methodology

Strong practices include:

- a pinned compiler and EVM harness;
- byte-level comparison of returns, reverts, events, and storage;
- a fail-closed AST importer;
- separate acceptedness/rejection fixtures;
- minimized permanent witnesses for found divergences;
- a chronological divergence log; and
- feature coverage tracked below AST node kinds.

The divergence history is especially informative. Recurring bug classes
include:

- calls hoisted in the wrong evaluation order;
- narrow integer cleanup omitted on one lowering path;
- storage reference versus storage value confusion;
- failure to materialize dynamic storage values at ABI/hash/revert boundaries;
- compiler-pipeline behavior accidentally mixed between legacy and via-IR;
- alias binding performed too late; and
- one unsupported function poisoning executable lowering of a whole contract.

## Metatheory and limits

The reviewed source contains substantial internal proofs, notably fuel
stability and world-adoption laws. There is no theorem relating imported
Solidity execution to `solc` output, Yul, or EVM bytecode. Differential testing
is therefore the evidence for compiler agreement.

The model also sometimes deliberately follows a selected pipeline rather than a
single uniform notion of Solidity. Historical notes show that mixing legacy and
via-IR behavior can easily produce an inconsistent profile. Solidity-HOL should
make the selected profile explicit per fixture and avoid silently taking the
more permissive behavior from one pipeline and evaluation behavior from
another.

## Lessons for Solidity-HOL

### Adopt

- Pinned, replayable solc/EVM differential fixtures.
- A fail-closed importer and explicit exclusion register.
- Separate acceptedness and runtime agreement tests.
- Concrete slot-level storage with typed layout interpretation.
- Captured storage locations for references.
- Intrinsic per-construct evaluation schedules preserved by elaboration.
- Exact observable comparison and a permanent divergence log.
- A strong fuel-stability statement that accounts for external interaction.

### Treat cautiously

- Duplicated frontend/type/lowering logic can become the dominant source of
  semantic errors.
- Very broad early feature coverage makes proof and refactoring surfaces large.
- An abstract memory model is appropriate initially, but cannot justify exact
  inline-assembly or compiler-memory claims.
- Differential agreement must not be described as a compiler-correctness proof.
- Profile boundaries must remain coherent when legacy and via-IR differ.

## Questions to revisit

- Can Solidity-HOL consume more compiler annotations and use a substantially
  smaller elaborator without losing test coverage?
- Should calls be represented directly inside the fuel interpreter, or should
  the interpreter produce an explicit interaction tree?
- Which source constructs should use canonical language order rather than
  legacy-compiler order?
- Can elaboration validity be expressed as a compact predicate that rules out
  the classes of lowering inconsistency found here?
