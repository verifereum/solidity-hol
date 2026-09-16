# `powdr-labs/yul-semantics`

Reviewed revision: `c9914c13df47efe026376723acd632bc33bc16e3`.

Repository: <https://github.com/powdr-labs/yul-semantics>

## Goal and boundary

`yul-semantics` is a Lean 4 formal semantics for Yul. It deliberately excludes
the future optimizing compiler and target EVM bytecode semantics. The core is
parameterized by a dialect supplying values, machine state, literal
interpretation, builtins, and effect classifications.

Yul's small grammar permits a correspondingly compact deep AST. Builtin calls
carry a dialect-specific operation enum, while user functions retain names.
Argument order is the Yul-specified right-to-left order, with result values
returned in source parameter order.

## Relational semantics

The authoritative semantics is a big-step inductive relation. Five conceptual
judgments—expressions, argument lists, statements, statement lists, and loop
iterations—are encoded as one indexed `Step` relation. This avoids awkward
mutual-induction support and permits ordinary rule induction for metatheory.

Machine state is abstract at the core level. Control outcomes explicitly
include normal execution, break, continue, function leave, and halt. Invalid
program configurations simply have no derivation.

## Executable interpreter and fuel

A total fuel-indexed interpreter mirrors the relation for an executable dialect.
Fuel bounds every recursive call, including syntax traversal, list traversal,
function calls, and loop iterations. Results distinguish success, stuckness,
and fuel exhaustion.

The project proves:

- interpreter soundness at every fuel;
- completeness of the interpreter for every derivation at all sufficiently
  large fuels; and
- an adequacy equivalence combining the two.

Completeness is stated as `exists N, forall n >= N`, building fuel stability into
the theorem rather than proving a separate monotonicity lemma. Determinism is
proved for dialects with deterministic builtins.

This is a clean alternative to making the interpreter primitive. Solidity-HOL
currently favors the interpreter as the primary user-facing definition, but
should preserve the option of defining a relational characterization and
proving equivalence later. At minimum, the sufficiently-large-fuel theorem is a
useful target stronger than a one-step monotonicity statement.

## EVM dialect and observations

The EVM-flavored dialect uses 256-bit bitvectors and provides memory, storage,
transient storage, environment operations, logs, calls, creation, and halting
operations. Gas costs are intentionally omitted, although active-memory size is
tracked because `msize()` is observable.

Raw frame execution retains mutations performed before a halting builtin. A
separate committed-state observation rolls changes back for revert, invalid,
and invalid-memory-access outcomes, while retaining halt kind and exposed
return data. Successful return, stop, and selfdestruct commit. This explicit
separation between execution state and caller-observable committed state is an
important design pattern for Solidity-HOL.

## Open-world calls

Calls and creation are supplied as relations from requests and pre-states to
completed responses. They can summarize arbitrary nested execution and
reentrancy. The semantics fixes caller-observable boundary behavior such as
copy-in, commit or rollback, returndata, static restrictions, and success words.

This open-world dialect is intentionally not executable or deterministic. The
executable EVM dialect leaves calls, creation, and `gas()` stuck. Consequently,
the determinism and interpreter-adequacy theorems do not apply to programs using
those operations; only effect-classification soundness extends to the
open-world dialect.

Solidity-HOL has chosen a different initial route: delegate calls to an
executable Verifereum EVM. This should preserve determinism for a fully supplied
world and transaction context. Nevertheless, the relational call boundary is a
useful specification of what an abstract environment is allowed to do and may
support compositional reasoning independently of concrete bytecode.

## Effect system

Each builtin is classified by determinism, reads, writes, and halting behavior.
The EVM dialect proves these flags soundly over-approximate builtin semantics.
This supports optimizer reasoning without baking EVM operations into generic
Yul transformations.

An analogous effect summary could eventually help Solidity-HOL state
evaluation-order independence or safe elaboration transformations. It should
not be required for the initial interpreter.

## Compiler-correctness stance

The planned compiler theorem is conditional on gas: a terminating source Yul
execution is simulated by target EVM execution, which either runs out of gas and
rolls back or, with sufficient gas, produces the same functional observation.
Gas remains only in the target machine.

This is relevant to Solidity-HOL's longer-term source-to-EVM story. A gas-free
source interpreter can still support a meaningful compiler theorem, provided
out-of-gas behavior and rollback are stated explicitly on the target side.
`gasleft()` and explicit gas forwarding require separate profile assumptions or
an oracle tied to the concrete target execution.

## Lessons for Solidity-HOL

### Adopt

- Distinguish stuck/invalid input from fuel exhaustion and language-level
  reversion.
- Aim for a sufficiently-large-fuel stability or completeness theorem.
- Keep control outcomes explicit.
- Separate raw execution from committed frame observations.
- Give external calls a precise boundary even when their internal execution is
  delegated.
- Consider an effect classification later for order-independence and compiler
  transformations.
- Keep dialect/EVM-version dependencies outside generic control semantics where
  practical.

### Different choices are justified

- Relational primacy is attractive for Yul compiler proofs, but Solidity-HOL
  needs executable differential testing from the beginning.
- Leaving external calls stuck is unsuitable for Solidity-HOL's planned
  EVM-backed interaction tests; Verifereum provides an executable choice.
- A single generic dialect interface is easier for Yul's small untyped core than
  for Solidity's analyzed types, locations, inheritance, ABI, and compiler
  profiles.

## Questions to revisit

- Should Solidity-HOL define a big-step relational characterization after the
  interpreter stabilizes and prove adequacy in the other direction?
- Can Verifereum external execution be abstracted by a relation while retaining
  the executable instance as a deterministic implementation?
- Which frame-boundary rollback operations should live in Verifereum and which
  are required around source-interpreted entry points?
