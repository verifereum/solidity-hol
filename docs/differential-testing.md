# Differential execution

`tools/run_differential.py` checks the maintained corpus in
`testdata/differential/corpus.json`. Each suite supplies a compiler artifact,
source unit and deployed contract; each case is a transaction to the contract
with initial storage and an expected result, final storage and logs.

A case calls either a named function with arguments (`function`, `args`),
encoded after its selector, or raw `calldata`. Optional `sender` (default
`0x2000`) and `value` (default 0) set the transaction's sender and value, and
`logs` lists the expected logs as `{"logger": ..., "topics": [...], "data":
"0x..."}`, the logger the contract unless given (default: none). A suite may
name a `peer`, a contract (`source`, `contract`, `artifact`) whose deployed
code sits at `0x5000` with the case's `peer_storage`, for the contract to call;
the evaluator's high-level calls run it, and any call back into the contract,
as bytecode in Verifereum. The evaluator runs the same calldata
through the elaborated program's dispatcher (`solidityEntry`), so selector
lookup, payability, argument decoding, `receive` and `fallback` are compared
too. Raw calldata declares no return types, so its `return` expectation is
`[]`.

A case with `"deploy": true` and the constructor's `args` is a creation
instead: Verifereum runs a creation transaction whose data is the artifact's
initcode followed by the encoded arguments, and the evaluator runs the
program's creation procedure (`deploy_contract`) on the encoded arguments, at
the address the transaction creates (`address_for_create` of the sender at
nonce 0). Both observe that account, which starts with no code or storage,
so `storage` must be empty and `logger` names that address. A successful
creation is observed as returning no data, so its `return` expectation is
`[]`; the deployed code is not compared. The HOL corpus theory proves one
`differential_agrees` theorem per case. Diagnostic failures and exhausted fuel
are inconclusive, never agreement.

The artifact goes through `solidityPrepareLib.prepare_artifact`, which checks
the pinned compiler/profile/settings contract, validates and elaborates the
source, and checks the full core program. The evaluator executes that core;
Verifereum executes the recorded bytecode. This comparison does not certify
the compiler or its artifact producer.

Both runs return an outcome, the complete committed storage of the tested
contract and the logs. Source frame completion rolls back writes on panic or revert before
comparison. The verdict compares total word-to-word storage functions by HOL
equality, so agreement includes every slot, including unlisted mapping keys and
cleared slots. The existing Verifereum from/to theorem and HOL's generic cv
equality rule evaluate this equality using the canonical sparse encoding,
which omits zero entries.

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
