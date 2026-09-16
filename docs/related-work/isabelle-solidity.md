# Isabelle/Solidity

Reviewed artifact: Archive of Formal Proofs entry “Isabelle/Solidity — A
shallow Embedding of Solidity in Isabelle/HOL,” current AFP release downloaded
August 2026. The AFP entry is dated February 25, 2026.

Entry: <https://isa-afp.org/entries/Isabelle-Solidity.html>

## Goal and semantic style

Isabelle/Solidity is primarily a source-level verification framework. Solidity
programs are written using shallowly embedded state-monadic combinators rather
than imported into a deep AST consumed by a general interpreter. Custom
Isabelle commands support contract declarations and verification, and a weakest
precondition calculus supplies verification conditions.

This is a materially different goal from Solidity-HOL's planned executable,
compiler-AST-driven semantics. Its main value for us is its treatment of
references and its proof-facing interface.

## State monad and nontermination

Computations use a partial state-exception monad. Execution can produce:

- a normal value and state;
- an exception and state; or
- nontermination (`NT`).

General loops are defined using Isabelle's partial-function package. The WP
calculus is a partial-correctness calculus: its definition makes the
nontermination case true. This avoids fuel in user verification, at the cost of
not being a total executable interpreter over arbitrary imported Solidity
programs.

Expressions and statements are directly composed as monadic HOL terms.
Evaluation order is therefore the order of monadic binds. Binary operations are
left then right. Assignment definitions explicitly evaluate the right-hand side
before index expressions, and comments connect that choice to Solidity
experiments.

## Values and locations

The modeled scalar types are comparatively small:

- Boolean;
- one 256-bit unsigned integer form;
- addresses; and
- fixed bytes represented as strings.

Runtime expression values distinguish:

- scalar values;
- memory locations;
- calldata pointers;
- storage pointers; and
- an empty/unit-like result.

Memory is an abstract graph-like list of scalar or array cells. Calldata and
storage are recursive typed trees. Stack variables can contain values or
references. Assignment definitions encode the principal copy and alias cases
between stack, memory, calldata, and storage.

This provides a clear shallow account of data-location behavior, but it is not a
concrete EVM representation:

- storage is keyed by contract address and source identifier;
- arrays and mappings are recursive mathematical values;
- slot packing and Keccak-derived storage locations are absent; and
- memory is not EVM byte-addressed memory.

## Calls and world model

State contains memory, calldata, storage, stack, and balances. Internal calls
save and restore the stack. External calls save and restore stack, memory, and
calldata, while an abstract locale parameter supplies the external computation.
Transfer performs balance changes before invoking that abstraction.

This gives useful compositional hooks but does not supply an EVM-grounded
open-world call/create semantics with concrete rollback, returndata, gas, and
reentrancy behavior.

## Program logic

The strongest reusable contribution for Solidity-HOL is the proof layer:

- a weakest-precondition definition with normal and exceptional postconditions;
- a library of WP rules for monadic primitives and Solidity combinators;
- Eisbach `wp` and `vcg` methods;
- memory footprint/location lemmas; and
- case studies proving contract invariants and functional properties.

The shallow embedding allows Isabelle simplification and higher-order logic to
act directly on programs. That greatly reduces the infrastructure required for
verification of programs written in the embedding.

## Validation and scope

The AFP artifact contains unit tests and case studies for a bank, token, casino,
voting contract, and simple auction. It is proof-checked as an Isabelle AFP
entry. It does not appear intended as a conformance model for current complete
Solidity, and it does not import upstream analyzed AST or differentially execute
the upstream semantic test suite.

Consequently, proof-checking validates the framework's internal theorems but
does not establish correspondence with arbitrary `solc` programs.

## Lessons for Solidity-HOL

### Adopt

- Separate normal and exceptional postconditions in the eventual program logic.
- Provide proof-oriented combinators and automation above the executable
  semantics rather than expecting users to unfold an interpreter.
- Preserve explicit memory/storage/calldata reference categories.
- Develop footprint and frame lemmas for abstract source memory.
- Treat nontermination deliberately: fuel is suitable for execution, while a
  later partial-correctness logic should not force users to reason about a
  particular fuel amount.

### Do not adopt as the primary semantics

- A shallow embedding cannot by itself serve our compiler-AST import and
  differential-conformance goals.
- Identifier-keyed typed storage is not sufficiently grounded for upgradeable
  layout, packed slots, arbitrary EVM callees, or compiler correctness.
- The narrow value/type subset is not an appropriate initial claim for a living
  current-Solidity semantics unless exclusions are made explicit.

## Possible future relationship

Solidity-HOL can combine the two styles: retain a deep elaborated AST and
fuel-indexed executable interpreter as the semantic foundation, then derive a
shallow proof interface or WP rules for verified programs. Isabelle/Solidity
provides evidence that such a user-facing layer can make realistic invariant
proofs substantially more manageable.
