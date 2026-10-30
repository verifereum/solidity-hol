(* The differential regression corpus, testdata/differential/corpus.json: every
 * case is a kernel-checked differential_agrees theorem relating the deployed
 * bytecode from the pinned compiler to the elaborated source. The build fails
 * if any suite or case does not agree. See docs/differential-testing.md.
 *)
Theory solidityDifferentialCorpus
Ancestors
  solidityDifferential
Libs
  solidityDifferentialLib

(* Read by holbuild's dependency scanner, which stages the corpus; it must list
 * the corpus and every artifact the corpus names, which
 * tools/run_differential.py checks.
 *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [
  "../testdata/differential/corpus.json",
  "../testdata/frontend/expected/pure_core.json",
  "../testdata/differential/expected/scalars.json",
  "../testdata/differential/expected/control.json",
  "../testdata/differential/expected/calls.json",
  "../testdata/differential/expected/storage.json"
]

val () = run_corpus {root = "..", corpus = "testdata/differential/corpus.json"}
