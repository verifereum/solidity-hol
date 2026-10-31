# Differential execution

`tools/run_differential.py` checks the maintained corpus in
`testdata/differential/corpus.json`. Each suite supplies a compiler artifact,
source unit and deployed contract; each case supplies arguments, initial
storage and an expected result. The HOL corpus theory proves one
`differential_agrees` theorem per case. Diagnostic failures and exhausted fuel
are inconclusive, never agreement.

The artifact goes through `solidityPrepareLib.prepare_artifact`, which checks
the pinned compiler/profile/settings contract, validates and elaborates the
source, and checks the full core program. The evaluator executes that core;
Verifereum executes the recorded bytecode. This comparison does not certify
the compiler or its artifact producer.

Both runs return an outcome and the complete committed storage of the tested
contract. Source frame completion rolls back writes on panic or revert before
comparison. Verifereum storage is a total word-to-word function; its canonical
sparse cv encoding omits zero entries. The proved injectivity of that encoding
makes cv equality a complete storage comparison, including unlisted mapping
keys and cleared slots.

The expected store is the initial store with the case's final entries applied;
all unspecified slots are zero. Selected slots (variable roots and explicitly
listed initial/final slots) remain in diagnostic payloads and the existing
projection theorem. A complete-storage mismatch can therefore display equal
selected-slot lists. The negative mapping regression demonstrates this case.

Run the same checks as CI with:

```sh
python3 tools/run_differential.py -j8 --allow-cached \
  -- --skip-checkpoints --skip-proof-steps
holbuild -j8 build --skip-checkpoints --skip-proof-steps solidityHolTheory
```

Pass `--solc /path/to/pinned/solc` to reproduce the compiler artifacts as well.
The upstream `semanticTests` acceptance report is a separate preparation check;
it does not execute those tests' call expectations.
