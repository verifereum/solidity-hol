(* PROTOTYPE. The core-to-HOL translator on functions of the differential
 * corpus: narrow arithmetic (add), two results (divmod), recursion (fact),
 * a while loop with break and continue (count), a for loop (sum) and a
 * do-while loop (doubleUntil). *)
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

fun eval_rhs tm =
  rhs (concl ((REWRITE_CONV [corpus_pure_core_unit_def] THENC EVAL) tm))

(* The function's id, and the names of its variables by declaration id *)
fun source_function name =
  let
    val f = eval_rhs “THE (unit_function corpus_pure_core_unit
                                         ^(stringSyntax.fromMLstring name))”
    val id = numSyntax.int_of_term (eval_rhs “(^f).fn_info.node_id”)
    val vars = HOLset.listItems (HOLset.addList (empty_tmset,
                 find_terms (fn t => type_of t = “:src_variable”) f))
    fun named v =
      SOME (numSyntax.int_of_term (eval_rhs “(^v).var_info.node_id”),
            stringSyntax.fromHOLstring (eval_rhs “(^v).var_name”))
      handle HOL_ERR _ => NONE
  in (id, List.filter (fn (_, s) => s <> "") (List.mapPartial named vars)) end

fun corpus name termination loop =
  let val (id, names) = source_function name in
    translate {env = “corpus_env”, lookup = lookup, name = name, id = id,
               names = names, termination = termination, loop = loop}
  end

val _ = corpus "add" NONE NONE

val _ = corpus "divmod" NONE NONE

val _ = corpus "fact" NONE NONE

val _ = corpus "count" NONE
  (SOME (WF_REL_TAC ‘measure (λ(n, c, i). n - i)’ >> rw[uint_add_def]))

val _ = corpus "sum" NONE
  (SOME (WF_REL_TAC ‘measure (λ(n, s, i). n - i)’ >> rw[uint_add_def]))

val _ = corpus "doubleUntil" NONE
  (SOME (WF_REL_TAC ‘measure (λ(n, k). n - k)’ >> rw[uint_add_def]))
