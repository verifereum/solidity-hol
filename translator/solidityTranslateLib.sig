(* PROTOTYPE core-to-HOL translator *)
signature solidityTranslateLib =
sig
  include Abbrev

  (* translate {env, lookup, name, id, names, termination, loop} defines
   * name, the shallow function of procedure id of the program environment env,
   * and proves and saves name_correct: the evaluator computes it. A loop
   * gets a helper name_loop with its own theorem name_loop_correct.
   *
   * lookup evaluates lookup_procedure env (AstId id); names gives the
   * variables' names by declaration id; termination proves the definition's
   * termination when Define cannot; loop proves the loop helper's.
   * Callees must be translated first. *)
  val translate :
    {env : term, lookup : conv, name : string, id : int,
     names : (int * string) list, termination : tactic option,
     loop : tactic option} -> thm
end
