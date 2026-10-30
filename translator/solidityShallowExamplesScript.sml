(* PROTOTYPE. The core-to-HOL translator on functions of the differential
 * corpus: arithmetic with two results (divmod), recursion (fact) and a loop
 * with continue (sum). *)
Theory solidityShallowExamples
Ancestors
  solidityCoreWf solidityShallow solidityEvaluator solidityDifferentialCorpus
Libs
  solidityTranslateLib

Definition corpus_env_def:
  corpus_env = core_program_environment [] corpus_pure_core_program
End

val lookup =
  REWRITE_CONV [lookup_procedure_def, corpus_env_def,
                core_program_environment_def, corpus_pure_core_program_def]
  THENC EVAL

fun corpus name id names termination loops =
  translate {env = “corpus_env”, lookup = lookup, name = name, id = id,
             names = names, termination = termination, loops = loops}

val _ = corpus "divmod" 150 [(132, "a"), (134, "b"), (137, "quot"), (139, "rem")] NONE []

val _ = corpus "fact" 130 [(110, "n"), (113, "res")] NONE []

val _ = corpus "sum" 91 [(64, "n"), (67, "total"), (70, "i")] NONE
  [WF_REL_TAC ‘measure (λ(n, total, i). n - i)’ >> rw[uint_add_def]]
