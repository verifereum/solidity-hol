# Initial compiler frontend boundary

This document records observations from the initial Solidity 0.8.37 via-IR
reconnaissance corpus. It is evidence for the imported and elaborated HOL
representations, not a claim of complete AST coverage.

The reproducible artifact is
[`testdata/frontend/expected/reconnaissance.json`](../testdata/frontend/expected/reconnaissance.json).
It is generated with:

```sh
tools/export_solc_artifacts.py \
  --solc /path/to/solc-0.8.37 \
  --output testdata/frontend/expected/reconnaissance.json \
  testdata/frontend/types.sol \
  testdata/frontend/evaluation_order.sol \
  testdata/frontend/storage_references.sol
```

The pure-subset importer fixture
[`testdata/frontend/expected/pure_core.json`](../testdata/frontend/expected/pure_core.json)
is generated the same way from `testdata/frontend/pure_core.sol`.

## Boundary layers

The implementation should distinguish three representations:

1. raw Standard JSON and the compiler-produced analyzed AST;
2. a validated, normalized AST retaining source and declaration identity; and
3. a smaller executable core with explicit effect schedules and operations.

The raw AST is trusted input initially, but it is not directly executable.
Import must reject unknown forms and missing required annotations.

## Identity and source positions

Every observed AST node has a numeric `id`, a `nodeType`, and a compact `src`
range. Declarations are referenced through numeric `referencedDeclaration`
fields. Source-unit `exportedSymbols`, variable `scope`, function `scope`, and
`linearizedBaseContracts` also contain declaration IDs. Names are therefore
diagnostic data, not semantic identity.

A normalized program will need distinct HOL wrappers or disciplined uses for at
least source IDs, node IDs, declaration IDs, and contract IDs. Import must check
that referenced IDs exist and have the expected declaration kind.

## Types and locations

Expressions and declarations carry `typeDescriptions` with both a display
`typeString` and an encoded `typeIdentifier`. Type-name subtrees provide
structural information through nodes such as `ElementaryTypeName`,
`ArrayTypeName`, `Mapping`, and `UserDefinedTypeName`.

The corpus confirms that semantic distinctions occur across several fields:

- declarations have `storageLocation`;
- type identifiers distinguish storage references, storage pointers, memory
  pointers, and calldata pointers;
- the display string is context-dependent and sometimes omits a location that
  appears in the identifier;
- user-defined types refer to their declarations by ID; and
- literal types include rational compile-time constants rather than only runtime
  integer types.

The importer must not treat `typeString` as a canonical type grammar. It should
construct normalized types from structural nodes, declaration links, location
annotations, and validated type identifiers. Encoded identifiers remain useful
for consistency checks and for distinctions not represented structurally at a
particular node.

The initial corpus includes integers, addresses, fixed bytes, dynamic arrays,
mappings, structs, enums, a user-defined value type, tuples, and internal and
event function types. It does not establish complete coverage of function
pointer types, fixed arrays, strings, dynamic bytes, payable addresses, contract
types, or every literal category.

## Expressions and calls

Observed expression nodes include identifiers, literals, member and index
access, tuple expressions, assignments, binary operations, and function calls.
The AST already supplies useful analyzed annotations:

- identifiers and most member accesses have `referencedDeclaration`;
- calls distinguish `functionCall`, `structConstructorCall`, and
  `typeConversion` through `kind`;
- binary operations provide `commonType`;
- expression nodes record `isConstant`, `isLValue`, `isPure`, and
  `lValueRequested`; and
- calls record positional arguments, optional argument names, and `tryCall`.

Not every builtin member operation has a declaration ID. In the corpus,
array `push` and `pop` are member accesses with no `referencedDeclaration` and
must be recognized from the receiver type and member name. Type conversions use
an `ElementaryTypeNameExpression` rather than a declaration reference.

The AST does not contain a general, normative evaluation-order annotation.
Argument arrays preserve source positions, but that alone is not a compiler
schedule. Profile elaboration must assign construct-specific schedules. The
emitted IR is useful evidence for Solidity 0.8.37 via IR, but compiler-generated
IR is not initially a stable frontend interface.

## Statements and declarations

The corpus currently observes blocks, expression statements, variable
declaration statements, returns, and event emission. A variable declaration
statement separately records declaration nodes and an `assignments` list of IDs;
this is important for tuple declarations and holes even though the current
corpus contains only single declarations.

Function definitions already record visibility, mutability, kind, virtuality,
parameters, return parameters, modifiers, implementation status, and optional
selectors. Contract definitions record inheritance-related and used-event/error
metadata. The current corpus has no inheritance clauses or modifiers, so their
resolution requirements remain to be established by later reconnaissance.

## Storage layout

`storageLayout` is separate from the AST. It contains state-variable entries
with declaration IDs, slots, byte offsets, contract names, and references into a
layout type table. Type-table entries describe encodings such as `inplace`,
`mapping`, and `dynamic_array`, byte widths, member offsets, keys, values, and
base element types.

Source types and layout descriptors must remain separate formal structures. The
compiler initially supplies layout calculation; Solidity-HOL interprets the
layout when reading, writing, and capturing references. The declaration IDs in
layout entries must resolve to compatible state-variable declarations.

Storage declarations now include elementary scalars, structs, scalar-key
mappings, and fixed/dynamic arrays, including their storage combinations.
Scalar leaves can be read and updated through member/index paths.
The importer takes each
contract's `storageLayout.storage` entries in declaration order, with their
slot, byte offset and type identifier; `valid_src_unit` requires one entry per
state variable, naming its declaration and type, and leaves the layout
calculation itself, including that packed variables don't overlap, to the
compiler. Elaboration copies slot and offset into the core program's
`state_variables`. Public state variables, initialisers, constants and immutables
are import errors. Mapping key/value types come from recursive type-name
normalization. AST and layout type identifiers use different encodings; both
are checked against the normalized type. The scalar leaf width determines
its storage read/write, and aggregate root slots come from the layout. Fixed
array dimensions come from the compiler's resolved integer type of the length
expression. Scalar elements pack without straddling slots; each nested row
starts on a fresh slot. Array indexing checks bounds with panic `0x32`, and
`.length` still evaluates its indexed prefix. Dynamic-array length is read from
its root slot and packed elements start at Keccak-256 of that slot. `push(value)`,
`push()` (also as a scalar lvalue), and `pop()` use the captured location. Empty
pop panics with `0x31`; both push forms follow the pinned compiler's resource
panic `0x41` at length >= `2^64`. Length reads and indexing retain the full
256-bit range. `pop()` clears only the removed scalar bytes; `push()` preserves
existing bytes at the appended position, as the pinned compiler does. Dynamic
array mutation of aggregates, memory/calldata references, local reference
bindings and aggregate copies remain coverage work.

Struct declarations may be file-level or contract members. User-defined type
names and field accesses retain declaration IDs; field ownership and expression
types are checked against the declared struct. Struct fields use solc's storage
pointer identifiers where state variables use storage reference identifiers.
The importer preserves that distinction and ignores only the display name
inside a struct type identifier, retaining its declaration ID and location.
`storageLayout.types` supplies each used struct's ordered members, relative
slots/offsets and size. Member IDs/types must match the declaration; sizes must
be positive multiples of a slot. Core layout checks reject fields outside the
struct's stride, scalar fields crossing a slot boundary, unaligned aggregates,
and cyclic inline containment. Layout calculation and byte disjointness remain
trusted compiler work. Unused declarations need no runtime layout.

The core program carries these struct layouts into its environment. Member
navigation extends an already captured base, and array strides use each struct's
whole-slot size. Elaboration rejects missing or inconsistent runtime layouts; the core checker
independently checks the elaborated program.

The selected compiler also emits `transientStorageLayout`. It is empty for the
initial corpus, so transient layout remains unvalidated.

## Normalized AST

`syntax/solidityImportScript.sml` defines the second layer for the admitted
pure subset, and `syntax/solidityImportLib.sml` imports it from an exporter
artifact, failing closed. The theory's header lists what `valid_src_unit`
establishes and what is left to elaboration; `tests/solidityImportTestScript.sml`
holds the positive fixture and negative fixtures derived from it.

## Elaboration

`semantics/solidityElaborateScript.sml` elaborates a valid unit of the pure
subset to `core_program`. Its header lists the admitted constructs and the
evaluation schedules, which were read from the via-IR output in
`testdata/frontend/expected/pure_core.json`. `tests/solidityElaborateTestScript.sml`
checks the elaborated fixture with `wf_core_program` and runs it in the
evaluator. The differential corpus runs the same inputs, and a wider corpus of
sources, through the deployed bytecode in Verifereum and requires equal
ABI-encoded outcomes; see [differential-testing.md](differential-testing.md).

## Required validation

Before elaboration, a well-formed imported program should at least establish:

- uniqueness and kind-correct resolution of declaration IDs;
- valid source-unit and scope references;
- structurally normalized types and explicit data locations where required;
- consistency between type nodes, type descriptions, and referenced
  declarations;
- resolved ordinary calls and explicitly classified builtin operations;
- arity and argument-name consistency;
- valid assignment targets and declaration-assignment links;
- complete contract linearization and dispatch metadata when those features are
  admitted; and
- complete, declaration-consistent storage layout metadata for storage-using
  contracts.

Anything outside the admitted node and annotation vocabulary must produce an
import error, not a partial semantic result.

## Open reconnaissance work

Before fixing a complete core AST, extend the corpus to cover control flow,
tuple holes, modifiers, inheritance and `super`, external calls, creation,
try/catch, errors, fallback/receive, dynamic and memory/calldata arrays, bytes/string, function
pointers, transient storage, and custom storage layout bases. The first HOL type
theory can begin from the normalized types already observed, provided unsupported
forms continue to fail closed.
