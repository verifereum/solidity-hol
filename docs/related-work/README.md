# Related Work

This directory records architectural reviews of recent formal Solidity and Yul
semantics. The purpose is to inform Solidity-HOL's design, not to rank projects
whose goals differ.

Reviews distinguish three kinds of evidence:

1. claims made by project documentation;
2. definitions and theorems inspected in the implementation; and
3. empirical validation against `solc` and EVM implementations.

A test corpus is valuable evidence of agreement on the tested programs, but it
is not a semantic correspondence theorem. Conversely, a machine-checked
metatheorem only applies to the definitions and hypotheses in its statement.

## Projects reviewed

| Project | Boundary and style | Execution/state | Validation and proofs | Primary relevance |
|---|---|---|---|---|
| [SolidCore (`solidity-lean`)](solidity-lean.md) | Real Solidity AST; deep surface AST, typechecking, lowering to an executable core | Fuel-indexed interpreter; concrete word-addressed storage; abstract memory; open-world interaction trees | Large differential corpus against pinned `solc` 0.8.35 and Foundry; fuel-stability and world-adoption laws, but no compiler-correctness theorem | Closest current architectural comparison |
| [Isabelle/Solidity](isabelle-solidity.md) | Shallow embedding of a Solidity subset into state-monadic Isabelle terms | Partial state-monad semantics; typed abstract storage/memory/calldata | AFP-checked WP/VCG infrastructure, unit tests, and verified case studies | Proof ergonomics and source-level program logic |
| [`yul-semantics`](yul-semantics.md) | Deep Yul AST parameterized by a dialect; relational big-step semantics | Derived fuel interpreter for executable dialects; abstract/open-world relational calls | Determinism, interpreter adequacy, effect soundness, and examples | Future Yul/compiler boundary and fuel metatheory |

These projects make different semantic claims. Isabelle/Solidity is primarily a
verification framework, `yul-semantics` is an IR semantics intended for compiler
proofs, and SolidCore pursues source-level conformance to a pinned compiler and
EVM profile.

## Common review questions

For each project we examine:

- the source, AST, or IR boundary;
- the upstream language/compiler revision;
- functional, relational, or shallow semantic style;
- termination and fuel;
- evaluation order;
- values, lvalues, references, and data-location copying;
- storage, memory, calldata, and EVM-world representation;
- calls, rollback, creation, and reentrancy;
- observable behavior and differential testing;
- proved metatheory; and
- maintenance and explicit exclusions.

## Provisional lessons for Solidity-HOL

1. **Keep the boundary fail-closed.** An importer and elaborator should reject
   unknown AST forms and metadata rather than silently assigning approximate
   behavior. Coverage should be tracked below the AST-constructor level because
   most difficult omissions are operators, call positions, type cases, and
   compiler annotations within otherwise supported nodes.
2. **Separate imported, checked, and executable syntax.** SolidCore's experience
   shows that compiler-faithful evaluation order and typed cleanup can be lost
   during lowering even when the interpreter rule is correct. The elaboration
   relation is part of the semantic trust boundary and needs its own tests and,
   eventually, validation theorems.
3. **Make order intrinsic to each elaborated construct.** Neither Solidity nor
   legacy `solc` has one global child-order switch. Calls hoisted out of
   expressions must preserve the original construct's order too.
4. **Use concrete EVM storage slots.** Solidity layout is observable and storage
   references capture concrete locations. In particular, dynamic path checks
   happen when a reference is bound; later dereference must not reconstruct and
   recheck the old path.
5. **An abstract memory heap remains viable initially.** Both current
   source-level projects abstract away compiler memory byte layout. Solidity-HOL
   can do likewise while still modeling aliasing, but must refine or bridge it
   before inline assembly or compiler-memory correspondence.
6. **State fuel theorems at the external-execution boundary.** A simple result
   monotonicity theorem is not enough once execution is an interaction tree.
   Fuel stability may need to quantify over every external answer so that the
   whole interaction tree is unchanged above sufficient fuel.
7. **Separate raw execution state from committed observations.** Revert rollback
   belongs at the correct call/frame boundary. The initial state and exposed
   return/revert data determine the observable state of a reverting frame.
8. **Differential failures are design evidence.** Minimized, permanent witnesses
   and a divergence log reveal recurring architectural errors—especially
   duplicated lowering paths, missing type cleanup, incorrect reference
   materialization, and evaluation-order changes.
9. **Record exclusions mechanically.** A versioned exclusion register is more
   reliable than prose and prevents unsupported programs from being counted as
   semantic agreement.
10. **Do not overstate validation.** Solidity-HOL should report separately:
    acceptedness coverage, executable test agreement, metatheory of the
    interpreter, and any eventual source-to-EVM correspondence theorem.

The conclusions above are tentative and will evolve as Solidity-HOL's own AST,
state interface, and test exporter are designed.
