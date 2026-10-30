(* PROTOTYPE core-to-HOL translator *)
signature solidityTranslateLib =
sig
  include Abbrev

  (* translate {env, lookup, name, id, names, termination, loops} defines
   * name, the shallow function of procedure id of the program environment env,
   * and proves and saves name_correct: the evaluator computes it. Each loop
   * gets a helper name_loopN with its own theorem name_loopN_correct.
   *
   * lookup evaluates lookup_procedure env (AstId id); names gives the
   * variables' names by declaration id; termination proves the definition's
   * termination when Define cannot; loops has one termination tactic per loop.
   * Callees must be translated first. *)
  val translate :
    {env : term, lookup : conv, name : string, id : int,
     names : (int * string) list, termination : tactic option,
     loops : tactic list} -> thm
end
