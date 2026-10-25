signature solidityDifferentialLib =
sig
  include Abbrev

  (* Runs the corpus file at the given path, a
   * solidity-hol-differential-corpus-v1 file whose paths are relative to the
   * repository root; root is the path of that root from the current
   * directory. For each suite it imports the source unit from its artifact,
   * defines corpus_<suite>_unit, _program and _code, and proves
   * corpus_<suite>_elaborates and corpus_<suite>_program_wf. For each case it
   * proves <suite>_<case>, a differential_agrees theorem. Every result is
   * printed as a line "differential-result: " followed by JSON; if any suite
   * or case fails, it raises an error after all have run.
   *)
  val run_corpus : {root : string, corpus : string} -> unit
end
