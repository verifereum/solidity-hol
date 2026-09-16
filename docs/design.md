# Solidity-HOL Design

## Status

This document records the initial design direction for Solidity-HOL. It is a
living document rather than a frozen specification. Decisions marked as
*tentative* are expected to be revisited as the executable semantics and test
coverage develop.

## Objective

Solidity-HOL aims to provide a formal and executable semantics for Solidity in
the HOL4 theorem prover. The project should support:

- reasoning about Solidity programs and multi-contract interactions;
- validation against the upstream Solidity semantic test suite;
- execution over the same EVM world-state model used by Verifereum;
- future compiler-correctness or translation-validation work; and
- continued evolution alongside the Solidity language and compiler.

In practice, Solidity's documented language and its compiler cannot be treated
as entirely separate targets. The documentation deliberately leaves some
behavior unspecified, while deployed programs obtain concrete behavior from a
particular compiler version, pipeline, settings, and EVM revision. We therefore
intend to describe versioned **Solidity execution profiles** while keeping the
shared language definitions independent of individual compiler revisions where
possible.

## Semantic boundary

The initial formal boundary is compiler-produced, analyzed Solidity AST and
associated metadata, not raw source text. Parsing, name resolution, overload
resolution, type inference, and storage-layout calculation are not initial
verification targets.

An imported program is expected to carry enough information to identify its
execution profile and resolve its semantics, including as applicable:

- the Solidity compiler revision and AST schema;
- resolved declaration references and expression types;
- data locations and call kinds;
- contract inheritance linearizations;
- storage and transient-storage layouts;
- ABI and contract metadata;
- the selected code-generation pipeline and relevant compiler settings; and
- the target EVM revision.

The compiler AST will be translated into a smaller elaborated HOL AST designed
for the semantics. This core AST should use stable declaration identifiers,
make resolved call kinds explicit, distinguish lvalues from ordinary
expressions, and retain the type and location information required at runtime.
A formal well-formedness predicate will state the assumptions made about
elaborated input rather than allowing arbitrary imported JSON to be interpreted
silently.

This is a trusted boundary initially. It should be possible to reduce that
trusted boundary later by formalizing or validating more of the frontend.

## Primary execution model

The primary semantics will be a deterministic, fuel-indexed definitional
interpreter. Fuel makes the definition total in HOL despite Solidity permitting
unbounded loops and recursive internal calls.

Source-level fuel is proof and execution machinery, not EVM gas:

- it is not observable through `gasleft()`;
- exhaustion produces a distinct nonterminal/resource result rather than an EVM
  out-of-gas result;
- increasing fuel should not change a terminal execution result; and
- actual gas behavior at an EVM execution boundary remains owned by the EVM
  semantics.

A central metatheoretic goal is a fuel stability result: once evaluation
terminates with sufficient fuel, giving it more fuel produces the same terminal
result and observable state.

The initial public semantics will not be defined primarily as a nondeterministic
relation or small-step machine. Explicit internal continuations or a CPS
interpreter may nevertheless be introduced if needed for efficient execution,
particularly with HOL4's `cv_compute`. Such an implementation should be related
to the direct definitional interpreter, as in Vyper-HOL.

## Expression evaluation order

Solidity documents the evaluation order of sibling expressions as unspecified,
apart from rules such as statement order and Boolean short-circuiting. The
compiler also does not implement one uniform order across all pipelines and
constructs. For example, the legacy and IR code generators differ for some
expressions, and the legacy generator's choices can depend on expression shape
and optimization settings.

To retain a deterministic and usable source semantics, Solidity-HOL will use a
canonical evaluation order, *tentatively left-to-right source order*, except
where a construct has a specific rule such as short-circuiting.

This canonical choice must not be presented as a guarantee made by every
Solidity compiler profile. Compiler-faithful import or elaboration may instead
make evaluation order explicit in the core AST. Thus the same surface AST may
elaborate differently for legacy and IR compiler profiles without complicating
the interpreter with nondeterministic evaluation.

Future work should define a conservative order-independence or commutation
condition and prove that canonical and profile-specific orders agree for
programs satisfying it. Programs whose observable behavior depends on an order
left unspecified by Solidity must be identified as profile-dependent.

## State and locations

### EVM world state

Persistent execution is grounded in the Verifereum EVM world state. Solidity
state operations act on the same accounts, balances, code, logs, persistent
storage, and transient storage used by EVM execution. This common substrate is
intended to support open-world and multi-contract reasoning without requiring a
Solidity-specific protocol framework.

### Storage

Solidity storage will be represented by concrete EVM storage words rather than
only by an abstract map from variables to typed values. Compiler-produced layout
metadata initially supplies the association between declarations, slots,
offsets, and layout types. HOL definitions will interpret that metadata and
formally implement:

- packed value reads and read-modify-write updates;
- structs and statically sized arrays;
- mappings and their Keccak-derived locations;
- dynamically sized arrays;
- short and long `bytes` and `string` encodings;
- inheritance and custom storage-layout bases; and
- transient-storage access where supported.

Layout *calculation* can remain trusted compiler input initially, while layout
*interpretation* and storage reads and writes belong to the formal semantics.
This allows tests to compare exact EVM storage before and after source-level
execution.

### Memory and calldata

The initial memory design is *tentatively* an abstract but addressable and
alias-aware Solidity heap, while calldata is represented concretely as bytes.
A source-level memory model must preserve Solidity's reference behavior: for
example, memory-to-memory assignment aliases, whereas storage-to-memory and
calldata-to-memory operations copy.

Using an abstract heap avoids making ordinary source semantics depend
immediately on compiler-specific allocation and byte-layout conventions. A
later refinement to concrete EVM byte-addressed memory will be needed for
inline assembly, exact compiler correspondence, and interactions that expose
memory representation.

Runtime values must therefore distinguish scalar values, tuples, and references
to storage, memory, or calldata. Tree-shaped arrays and structs alone are not
sufficient to model Solidity aliasing.

## Calls and EVM interaction

The Solidity interpreter evaluates source-level call operands and performs the
appropriate ABI encoding. Actual external message calls and contract creation
are delegated to Verifereum over the shared EVM world state. Verifereum should
own EVM mechanisms including:

- call-frame checkpoints and rollback;
- value transfer and account creation;
- call depth and actual gas accounting;
- static-call restrictions;
- return and revert data;
- creation and destruction rules; and
- transaction-scoped transient-storage behavior.

This boundary permits interaction with arbitrary bytecode contracts and
precompiles without assuming that their Solidity source is available.

Initially, after execution crosses into the EVM, nested execution—including
reentrancy—will execute as EVM bytecode. The source-level interpreter will not
recursively interpret target source as the primitive meaning of an external
call. Possible later extensions include an EVM callback for selected
source-interpreted accounts or compositional replacement of bytecode execution
using compiler-correctness theorems. The design should leave room for these
extensions without depending on them initially.

Internal Solidity calls, virtual dispatch, modifiers, and ordinary control flow
remain within the source interpreter. Deployment and external-call entry points
must wrap source execution with rollback behavior consistent with their EVM
counterparts.

## Results and observations

The evaluator should distinguish at least:

- successful completion and function return;
- revert with byte data;
- Solidity panic with its panic code;
- custom errors;
- invalid or unsupported semantic states;
- source-fuel exhaustion; and
- outcomes returned by delegated EVM execution.

The primary observable behavior used for testing and equivalence should include:

- success or revert data;
- ABI return values;
- logs;
- account balances and other relevant account changes;
- persistent and transient storage; and
- created accounts and deployed code where applicable.

Local variables and abstract source memory are normally internal rather than
cross-boundary observations. Exact gas behavior remains an important unresolved
part of the eventual observation model.

## Versioning and profiles

Every imported fixture or program should identify the upstream revision and
settings under which its metadata was generated. A profile is expected to
include at least:

- compiler revision;
- analyzed-AST schema revision;
- code-generation pipeline where observable behavior depends on it;
- EVM revision; and
- relevant compiler settings.

The repository should pin revisions used in CI and generated tests, while its
formal definitions should be extended rather than silently reinterpreted when
upstream behavior changes. Compatibility code and profile-specific elaboration
should be isolated from the core interpreter where practical.

Compiler bugs require care. Matching a particular released compiler can be a
useful compatibility result, but known buggy behavior must not silently become
the canonical language semantics.

## Testing strategy

The upstream `test/libsolidity/semanticTests` corpus will be the main source of
differential fixtures. An exporter should record the source, compiler profile,
analyzed AST, layouts, ABI, deployment/call sequence, and expected observable
results.

Generated HOL tests should be split into manageable theories. The project should
maintain an explicit coverage manifest by AST constructor and language feature,
as well as a documented list of expected exclusions. Small hand-written tests
will supplement the upstream suite for semantic boundaries such as:

- checked and unchecked arithmetic;
- fuel exhaustion and recursive calls;
- storage packing and nested storage paths;
- memory aliasing and location-changing copies;
- virtual and `super` dispatch;
- modifier execution;
- rollback across calls; and
- evaluation-order-sensitive expressions.

Where appropriate, fixtures should be exercised using both the legacy and IR
compiler pipelines. Agreement between both compiled executions and the source
semantics is useful evidence, while differences must be classified rather than
hidden.

## Tentative implementation stages

1. **Project and profile foundation**
   - Pin HOL4, Verifereum, Solidity, and EVM revisions.
   - Define execution-profile and imported-metadata types.
   - Establish build and test-generation infrastructure.

2. **Elaborated syntax and pure execution**
   - Define normalized types, declarations, expressions, lvalues, and statements.
   - Implement scalar values, conversions, checked/unchecked arithmetic, locals,
     tuples, control flow, fuel, and internal calls.

3. **Contracts and concrete storage**
   - Add EVM-backed state variables, storage layout interpretation, mappings,
     arrays, structs, events, public getters, immutables, and transient variables.

4. **Reference semantics**
   - Add memory, storage, and calldata references; copy-versus-alias rules;
     allocation; `delete`; and array/bytes operations.

5. **Inheritance and source-level dispatch**
   - Add C3 metadata use, virtual and base-qualified calls, `super`, modifiers,
     inherited constructors, interfaces, and libraries.

6. **ABI and inter-contract execution**
   - Add calldata dispatch, receive/fallback, high- and low-level calls, creation,
     CREATE2, try/catch, custom errors, rollback, and Verifereum integration.

7. **Advanced features and compiler work**
   - Address user-defined operators and function values, the Yul/inline-assembly
     boundary, concrete memory refinement, and compiler-correctness foundations.

These stages describe dependency order, not promises that each stage must cover
every feature before work begins on the next.

## Open questions

The following issues remain deliberately unresolved:

- the exact canonical evaluation order for every expression construct;
- the representation and supported fidelity of `gasleft()`, explicit call gas,
  and source-level out-of-gas behavior;
- the mechanism for replacing nested EVM bytecode execution with source
  semantics before compiler correctness is available;
- the point at which abstract source memory should be refined to EVM memory;
- treatment of inline assembly and Yul;
- the exact versioning granularity and compatibility policy for AST schemas;
- handling optimizer- or bug-dependent compiler behavior; and
- the final observational equivalence used by compiler-correctness theorems.

Changes to these choices should be recorded here with their consequences for
existing profiles, tests, and theorems.
