# Solidity-HOL

Formal and executable semantics for the [Solidity](https://soliditylang.org/)
programming language in the
[HOL4 theorem prover](https://hol-theorem-prover.org/).

This project is intended to support formal reasoning about Solidity programs,
validation against the upstream Solidity semantic tests, compositional
reasoning about interactions through an EVM world state, and future work on
compiler correctness.

## Planned approach

The initial semantics will operate on compiler-produced, analyzed Solidity AST
and metadata rather than raw source text. This includes resolved types and
declarations, inheritance information, ABI metadata, and storage layouts. The
imported representation will be elaborated into a smaller HOL AST with explicit
well-formedness assumptions.

Execution will primarily be defined by a deterministic, fuel-indexed
definitional interpreter. Fuel provides totality in HOL for recursive functions
and unbounded loops, but is separate from observable EVM gas.

Persistent state and external interaction will be grounded in the EVM semantics
provided by [Verifereum](https://verifereum.org/):

- Solidity storage operations will access concrete EVM storage slots;
- compiler-produced layout metadata will initially provide slot and offset
  assignments;
- external calls and contract creation will execute through the EVM over a
  shared world state; and
- EVM execution will own gas, call checkpoints, rollback, value transfer, and
  nested bytecode execution.

Solidity leaves sibling-expression evaluation order unspecified, and compiler
pipelines do not make one uniform choice. Solidity-HOL will therefore use a
canonical deterministic order—tentatively left-to-right—while allowing
compiler-profile elaboration to make different orders explicit when matching a
particular compiler pipeline.

The semantics and its generated test fixtures will be versioned against pinned
Solidity compiler and EVM revisions. The repository is intended to evolve with
upstream Solidity rather than describe only one permanently fixed release.

See [docs/design.md](docs/design.md) for the current design, implementation
stages, and open questions. The initial compiler profile is documented in
[docs/profiles.md](docs/profiles.md), and the current compiler-AST observations
are recorded in [docs/frontend-boundary.md](docs/frontend-boundary.md). Reviews
of relevant active semantics projects are collected in
[docs/related-work/](docs/related-work/README.md).

## Status

The project is currently in its design and frontend-reconnaissance phase. No
supported Solidity subset has been implemented yet.
