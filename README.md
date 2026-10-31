# Solidity-HOL

Formal and executable [Solidity](https://soliditylang.org/) semantics in
[HOL4](https://hol-theorem-prover.org/), using concrete EVM storage and execution
from [Verifereum](https://verifereum.org/).

## Execution pipeline

The semantic definition is compiler artifact → imported source unit →
`elaborate_unit` → ordered core → fuel-indexed evaluator. There is no separate
source-unit execution relation. Elaboration names effectful intermediate
results and fixes evaluation order for the pinned compiler profile; core
operands are pure bindings or constants. Fuel bounds recursive calls and loop
iterations independently of EVM gas.

`solidityPrepareLib.prepare_artifact` is the checked entry point for artifact
consumers. It checks the artifact format, compiler version/commit, profile and
Standard JSON settings against `SOLIDITY_PIN` and
`profiles/solc-0.8.37-via-ir-osaka.json`. It then imports and validates the source,
elaborates it, and checks the complete `wf_core_program` with `cv_eval`.
Success retains the checked artifact alongside the source/core terms and HOL theorems for source validation,
elaboration and core well-formedness. Artifact metadata checks run in SML;
they do not certify that the compiler produced the recorded output. The Python
runner's solc-free artifact checks provide earlier diagnostics; acceptance is
always decided by this SML preparation boundary.

Malformed artifacts, unsupported import/lowering, source-validation rejection
and invalid generated core have distinct diagnostics. Source validation also
contains supported-subset restrictions. Invalid generated core is an
implementation failure. Unexpected HOL evaluation failures propagate.

The raw importer and `elaborate_unit` remain available for reasoning and
frontend inspection. Their callers own the compiler/profile contract, source
validation and full core check. `prepare_unit` performs the semantic checks for
an already imported unit whose provenance the caller has established.

## Core and storage

A `core_program` owns its procedures, state variables, semantic type
declarations and storage layouts. `core_program_environment` derives the
checking/runtime environment from that program. Struct declarations describe
field identities and types even when there is no storage layout. Storage
layouts separately describe slots and offsets and must agree with the declared
fields. Enum and user-defined value declarations also live in the program;
their importer coverage is still deferred.

The evaluator executes elementary scalar operations and conversions, locals,
tuples, structured control flow, internal calls, built-in failures, packed
state values, scalar-key mappings, storage arrays and storage struct members.
Assignment, compound assignment, increment and tuple writes share local or
captured-reference destinations. `solidityStorage` owns packed access and
navigation; the evaluator owns bindings, frame checks and control flow.
Scalar writes, reference
rebinding and content copying are distinct core operations; the latter two
remain extension points rather than implemented aggregate semantics.

Memory/calldata execution and a memory model compatible with inline assembly
remain unresolved. Concrete CALL/CREATE boundary experiments exist separately;
connecting them to source execution still needs an external-call context/gas
contract. Core well-formedness alone does not rule out `InvalidCompletion`:
for example, a storage write in a static frame is deliberately invalid.

## Program proofs

`solidityTranslateLib.translate_unit` produces shallow HOL functions and
kernel-checked correspondence theorems for its supported core fragment. It
consumes maintained evaluator equations; the deep interpreter remains the
semantic definition. Normal paths through checked operations and internal calls
join before the rest of the block, preserving one continuation. Abrupt source
returns and failures retain their behavior.

See [translator.md](docs/translator.md) for the API, theorem preconditions and
current coverage. Storage proofs, memory/assembly and the source external-call
contract remain future work.

## Yul

The compiler's runtime Yul object has its own AST, EVM dialect, machine and
fuel-indexed evaluator in `syntax/yulAST`, `semantics/yulDialect`,
`semantics/yulState` and `semantics/yulEvaluator`;
`semantics/yulEvaluatorProps` proves that a run which does not run out of fuel
gives the same answer at any larger fuel. Input outside the modelled subset is
an explicit invalid outcome rather than a value; the two ill-formed inputs the
compiler rejects by itself — a `break` in a `for` loop's post block, and a call
returning several values in argument position — are accepted. The node kinds
and builtins the pinned compiler emits, per fixture, are enumerated in
[testdata/yul/reconnaissance.md](testdata/yul/reconnaissance.md).

## Validation

```sh
holbuild buildhol
holbuild -j8 build solidityHolTheory
python3 -m unittest discover -s tests -p 'test_*.py'
python3 tools/run_differential.py -j8
```

The differential corpus compares source evaluation with pinned compiler
bytecode in Verifereum, including complete committed contract storage. Slot
lists select diagnostics; they do not limit comparison. The upstream `semanticTests` coverage tool checks
preparation acceptance; it does not execute the tests' call expectations.
See [differential-testing.md](docs/differential-testing.md),
[profiles.md](docs/profiles.md) and
[semantic-tests-coverage.md](docs/semantic-tests-coverage.md).

See [implementation-blueprint.md](docs/implementation-blueprint.md) for module
ownership, evaluator interfaces and extension points.
