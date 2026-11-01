(* The three-way corpus run: the compiler's own Yul held to the expectations
 * the corpus theory already holds the elaborated core and the deployed
 * bytecode to. See yulDifferentialTheory and solidityDifferentialLib, and
 * docs/yul-differential.md for the report this produces.
 *
 * The Yul artifacts this reads are generated from the pinned compiler by
 * tools/run_yul_differential.py, which writes them here and then builds this
 * theory; they are not committed (the ASTs of the twelve suites are tens of
 * megabytes). The importer's own tests use the small committed fixture under
 * testdata/yul/expected (tests/yulImportTest).
 *)
Theory yulDifferentialCorpus
Libs
  solidityDifferentialLib yulImportLib

(* Read by holbuild's dependency scanner, which stages the corpus, its
 * artifacts and the generated Yul artifacts.
 *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [
  "../testdata/differential/corpus.json",
  "../SOLIDITY_PIN",
  "../profiles/solc-0.8.37-via-ir-osaka.json",
  "../profiles/solc-0.8.37-via-ir-osaka-optimized.json",
  "../testdata/yul/reduced.json",
  "../testdata/frontend/expected/pure_core.json",
  "../testdata/differential/expected/shadowed_builtins.json",
  "../testdata/yul/generated/pure_core.ir.json",
  "../testdata/yul/generated/pure_core.optimized.json",
  "../testdata/yul/generated/shadowed_builtins.ir.json",
  "../testdata/yul/generated/shadowed_builtins.optimized.json",
]

val () = solidityDifferentialLib.run_three_way
  {root = "..", corpus = "testdata/yul/reduced.json",
   yul_root = "testdata/yul/generated"}
