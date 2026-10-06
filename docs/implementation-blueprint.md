# Milestones 1–2: first implementation checkpoint

This is a **build-checked architectural blueprint and concrete EVM experiment**,
not a supported Solidity subset. The decisions in [interpreter-design.md](interpreter-design.md)
remain authoritative. No importer or source evaluator has been implemented.

## Buildable artifacts

| Theory | Purpose |
| --- | --- |
| `syntax/solidityCoreScript.sml` | Candidate ordered core, scalar/reference values, captured targets, procedures and control outcomes |
| `semantics/solidityStateScript.sml` | Candidate source state, separate gas evidence, observable EVM projection and frame completion |
| `semantics/solidityEVMCallScript.sml` | Concrete CALL/CREATE boundary experiment reusing pinned Verifereum |
| `tests/solidityEVMCallTestScript.sml` | CALL, STATICCALL, DELEGATECALL, precompile and failure witnesses |
| `tests/solidityEVMCreateTestScript.sml` | CREATE/CREATE2 installation, revert and collision witnesses |
| `tests/solidityEVMFrameTestScript.sml` | Nested rollback and sequential transient-storage witnesses |

All are ancestors of the project roll-up:

```sh
holbuild build solidityHolTheory
```

Definitions and proofs contain no cheats or new axioms. Concrete boundary
witnesses are proved by `cv_eval`, not merely evaluated outside HOL.

## Candidate core contracts

Effects are named by `DefineStmt`; its operands are pure constants or bindings.
Type annotations distinguish ordinary Solidity types from product types for
intermediate tuples/multiple return values. Tuple construction/projection is
explicit. These annotations are not yet checked by a well-formedness predicate.

Capture statements produce entries in a separate target map. The core then
explicitly writes a scalar, binds a reference (including memory reference
fields), or copies typed contents between references. A storage reference
captures backend, account, slot and byte offset, together with type/layout
identity. No stored index path is reevaluated.

Memory references use object identity and an abstract cell offset; this is not
an EVM byte address. The sparse heap separates metadata from cells, avoiding a
mandatory dense array representation. Calldata references capture an offset
and extent into frame calldata; nested ABI validation/navigation remains to be
defined. These are candidate representations, not established refinement laws.

`core_procedure` gives ordinary functions and elaborated modifier wrappers the
same invocation interface. Return bindings are explicit. Fresh invocation scopes
and explicit argument/return wiring must preserve via-IR repeated-placeholder
behavior; a body return is caught locally, not at the outer source frame.

`WhileStmt` contains an ordered condition prelude, condition atom and body, so
effectful conditions rerun every iteration. Break and continue are scoped
outcomes; future for/do-while normalization must preserve their distinct edges.
The operator vocabulary is intentionally incomplete. Unsupported source cannot
be admitted until its lowering and validation rules exist.

### Proposed evaluator signatures (not constants or axioms)

```text
eval_block     : num -> core_environment -> core_stmt list
                    -> source_state -> gas_observation list -> source_result
invoke_source  : num -> core_environment -> ast_id -> runtime_value list
                    -> source_state -> gas_observation list -> source_result
navigate       : core_environment -> reference -> navigation_value
                    -> source_state -> navigation_result
copy_contents  : core_environment -> sol_type -> sol_type
                    -> reference -> reference -> source_state -> copy_result
```

`core_environment` must supply validated declarations, resolved procedures,
source types and layout descriptors. Navigation/copy result types must preserve
state and report panic or invalid input distinctly. They are deliberately not
invented as total-success operations in this checkpoint.

Finite block traversal should use list recursion without decrementing fuel.
Potentially unbounded while iteration and recursive procedure invocation use the
smallest sufficient recursive-depth decrement. Siblings reuse the depth bound;
copy/navigation helpers use independent termination measures. No step-budget
counter is threaded through state. Fuel stability is a future proof, not yet a
claim about an evaluator that does not exist.

The bytecode boundary's concrete context supply is still unresolved. It must be
added to the evaluator interface in alignment with the intended/final Vyper-HOL
#98 solution. The schematic signatures above do **not** claim source state alone
can reconstruct an arbitrary EVM invocation state. They do not introduce a
replaceable handler or artificial EVM registers into source state.

### State, evidence and frame completion

Source state uses Verifereum account/transient-storage/event types, with source
scopes, captured targets, addressable heap and meaningful message fields.
`project_evm_world` projects only accounts, transient storage and current-frame
logs, failing on an empty context stack. Equality of this projection is a
necessary observable check, **not** a complete simulation relation.

Gas evidence is separate from world state. The tags reserve distinct gasleft,
call and creation observations; their exact meanings and oracle-consumption
rules await the aligned upstream design. Explicit requested gas is retained in
`bytecode_request`, not replaced by evidence.

`finish_source_frame` demonstrates commit versus restoring the entire initial
source world on revert/panic. Invalid/fuel outcomes expose no committed world.
It does not perform ABI encoding, transaction fees, deletion processing or gas
refund accounting. Its rollback theorem is about this wrapper, not interpreter
or EVM correspondence.

### Difficult-case walkthroughs

- **Captured storage then pop:** navigation captures an element slot once;
  bind the local to that reference; subsequent pop changes storage; reading the
  bound reference does not recheck the old prefix. Dangling cases are
  profile behavior/undefined-behavior witnesses, not portable guarantees.
- **Memory alias:** bind two locals to the same heap reference; member writes
  update the shared cells. Storage-to-memory copying allocates a separate object
  and uses the copy helper rather than rebinding.
- **Effectful assignment:** ordered definitions evaluate RHS and capture LHS in
  the chosen profile schedule; classified writes/copies follow afterward.
- **Modifier return:** placeholder calls an inner procedure; that invocation
  catches return and restores its binding scope; wrapper postlude continues.
  Revert/panic/resources propagate without postlude execution.
- **Bytecode reentry:** successful nested EVM effects update the shared account
  storage before later source reads. Concrete EVM-context supply and the source
  correspondence needed to justify this transition remain a separate obligation.

## Concrete EVM boundary experiment

`execute_boundary` takes an **existing concrete EVM execution state** positioned
at a CALL-family or CREATE-family opcode. Concrete operand stack, input/output
memory, caller gas and caller checkpoints are supplied by the fixture/context.
It never rebuilds transaction state from the observable source projection.

1. Check the parsed opcode position.
2. Execute Verifereum's handled `step` (including precompile completion).
3. If a child remains on the stack, execute `run_call` for that entered frame.
4. Otherwise return the entry result immediately; do not run the caller suffix.

`observe_boundary` retains the entire returned concrete state. A normal result
reports the caller's stack word and returndata: CALL success flag, or CREATE
address/zero. Nested revert/exception is ordinarily a normal return with word
zero; the precise nested halt reason is not recoverable from this low-level
result. A singleton caller-entry failure or domain/semantic abort retains the raw result.
A nested caller-entry exception can pop the caller itself and return normally to
its parent; `BoundaryCallerExited` retains that concrete state. The source driver
must not resume the exited source frame. The handled result does not reveal its
precise halt reason. Malformed results also retain their concrete state. Wrong
opcode position and no-result outcomes remain distinct checks at the experiment
boundary, not Solidity reverts.

The pinned dependency's `vfmDecreasesGasTheory.run_call_eq_tr` unconditionally
shows `run_call` returns `SOME`. `boundary_execution_has_result` reuses it; no
source fuel is added. Well-formedness is still required for upstream preservation
laws. The generic CALL fixture has a proved `wf_state` condition on code and
stack sizes; the nested outer-rollback fixture is separately proved well formed.
Do not infer preservation hypotheses for arbitrary caller checkpoints from
termination alone.

### Executed proof witnesses

- Returned byte 0x2a reaches caller memory and returndata; invalid caller suffix
  is not executed.
- Successful SSTORE persists; SSTORE followed by REVERT restores storage while
  retaining revert bytes.
- INVALID is a low-level failed call, not an adapter semantic abort.
- STATICCALL rejects SSTORE; DELEGATECALL writes the caller's storage.
- Empty-code calls succeed; identity precompile completion during entry does
  not accidentally execute the caller suffix. Insufficient balance returns a
  failed call; successful value transfer occurs once; domain errors remain
  semantic aborts rather than ordinary low-level failure.
- Nested caller-entry out-of-gas exits to its parent, retains the concrete state,
  restores storage and stops before the parent suffix.
- CREATE installs initcode-returned runtime bytecode; reverted initcode and
  address collision retain the creator's incremented nonce. CREATE2 uses the
  salt/initcode-derived address.
- An outer frame reverting after an inner successful call undoes inner storage
  changes through genuine nested EVM checkpoints.
- Two calls with the same transaction state preserve transient storage. The
  harness supplies the second operand stack, but resets no transaction fields.

Fixtures use bounded gas to test EVM mechanics. They make no compiler-equivalent
source gas claims. Exact gas/refunds/access-state laws, further domain and
value-transfer edge cases, bytecode reentry and full source correspondence need
additional witnesses/proofs. Creation fixtures execute real initcode but do not
constitute Solidity constructor/deployment semantics.

## Next gates and escalation points

1. Review the candidate representations before extending the core vocabulary.
2. Resolve concrete context supply and gas evidence against Vyper-HOL #98; do
   not silently choose a synthetic source-frame EVM context or fixed gas policy.
3. Define core well-formedness and the reference/layout environments; establish
   copy termination without fuel, including recursive-type restrictions.
4. Implement the minimal evaluator across loops/internal calls/modifier wrappers
   and prove fuel stability. Only then broaden source feature coverage.
5. Add value-transfer, domain-abort, reentry and bookkeeping witnesses to the
   adapter experiment and derive preservation under exact upstream hypotheses.

Milestone 1 is a compiled blueprint with schematic evaluator contracts, not a
complete interpreter interface. Milestone 2 has a working concrete boundary
experiment, not the final source adapter. Both intentionally stop short of
settling upstream-dependent architecture on the user's behalf.
