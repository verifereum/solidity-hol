(* Core-to-HOL translator; docs/translator.md describes it *)
signature solidityTranslateLib =
sig
  include Abbrev

  datatype outcome = Proved of thm | Unsupported of string | Failed of string
  type result = {name : string, outcome : outcome, seconds : real}

  (* translate_unit {prefix, unit_def, program_def, termination, loops}
   * translates every function of an imported unit, given unit_def, the
   * definition of a constant for the unit, and program_def, that of its
   * elaborated program. It defines prefix ^ "env", the program's environment,
   * and for each function f, callees first, the shallow function prefix ^ f
   * and the theorem prefix ^ f ^ "_correct" that the evaluator computes it;
   * a loop gets a helper prefix ^ f ^ "_loop" with its own theorem.
   *
   * termination and loops give, by function name, a tactic proving the
   * termination of the function's definition and of its loop helper when
   * Define cannot (for functions that call each other, under the first
   * one's name); a loop helper always needs one. A function the translator
   * does not cover yet is Unsupported, and so are its callers; so are
   * overloaded functions. Any other failure is Failed, a translator bug. *)
  val translate_unit :
    {prefix : string, unit_def : thm, program_def : thm,
     termination : (string * tactic) list, loops : (string * tactic) list} ->
    result list
end
