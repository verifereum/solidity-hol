(* The core-to-HOL translator on every function of every elaborated suite of
 * the differential corpus (testdata/differential/corpus.json). Each function
 * must translate and prove, or be one the translator does not cover yet; a
 * Failed one, one of the proved list that does not prove, or a proof slower
 * than max_seconds fails the build after every suite has run. Prints one
 * translator-result line per function.
 *)
Theory solidityTranslatorCorpus
Ancestors
  solidityDifferentialCorpus solidityShallow
Libs
  solidityTranslateLib

val max_seconds = 120.0

(* Termination of loop helpers, by suite and function *)
val loops = [
  ("pure_core",
   [("count", WF_REL_TAC ‘measure (λ(n, c, i). n - i)’ >> rw[uint_add_def]),
    ("sum", WF_REL_TAC ‘measure (λ(n, s, i). n - i)’ >> rw[uint_add_def]),
    ("doubleUntil", WF_REL_TAC ‘measure (λ(n, k). n - k)’ >> rw[uint_add_def]),
    ("checkedBranchOverwrite", WF_REL_TAC ‘measure (λ(a, b). a)’)])]

(* The functions that prove today, by suite: losing one fails the build *)
val proved = [
  ("pure_core",
   ["add", "argumentOrder", "badDivide", "checkedBranchOverwrite", "compoundOrder", "count", "divmod",
    "doubleUntil", "fact", "guardedDivide", "locals", "panicOrder",
    "shortCircuit", "sum", "swap"]),
  ("scalars", ["boolLogic", "increment", "subtract"]),
  ("builtins", ["localCondition"]),
  ("shadowed_builtins", ["require", "assert", "revert", "run"]),
  ("storage_arrays", ["combine"]),
  ("calls",
   ["ackermann", "argumentEffects", "decrementUnderflow", "fib", "holes",
    "minMax", "narrowSum", "operandPanics", "pair", "prefixPostfix", "rotate",
    "sameTarget", "swapThroughCall"])]

fun json_string s =
  let
    fun esc #"\"" = "\\\""
      | esc #"\\" = "\\\\"
      | esc c = if Char.ord c < 32
                then "\\u" ^ StringCvt.padLeft #"0" 4 (Int.fmt StringCvt.HEX (Char.ord c))
                else String.str c
  in "\"" ^ String.translate esc s ^ "\"" end

(* Every suite that elaborated has a program definition *)
val suites =
  Listsort.sort String.compare
    (List.mapPartial
       (fn (n, _) =>
          if String.isPrefix "corpus_" n andalso String.isSuffix "_program_def" n
          then SOME (String.substring (n, 7, size n - 7 - size "_program_def"))
          else NONE)
       (DB.definitions "solidityDifferentialCorpus"))

fun run suite =
  let
    val prefix = "corpus_" ^ suite
    fun def s = DB.fetch "solidityDifferentialCorpus" (prefix ^ s)
    val results =
      translate_unit {prefix = prefix ^ "_", unit_def = def "_unit_def",
                      program_def = def "_program_def", termination = [],
                      loops = case Lib.assoc1 suite loops of
                                SOME (_, l) => l
                              | NONE => []}
    fun line {name, outcome, seconds} =
      print ("translator-result: {\"suite\":" ^ json_string suite ^
             ",\"function\":" ^ json_string name ^
             (case outcome of
                Proved _ => ",\"status\":\"proved\""
              | Unsupported m => ",\"status\":\"unsupported\",\"message\":" ^
                                 json_string m
              | Failed m => ",\"status\":\"failed\",\"message\":" ^
                            json_string m) ^
             ",\"seconds\":" ^ Real.fmt (StringCvt.FIX (SOME 1)) seconds ^ "}\n")
    val () = List.app line results
    val must_prove = case Lib.assoc1 suite proved of SOME (_, l) => l | NONE => []
    fun failed {outcome = Failed _, ...} = true
      | failed {name, outcome = Unsupported _, ...} = mem name must_prove
      | failed {seconds, ...} = seconds > max_seconds
    val missing =
      List.filter (fn f => not (List.exists (fn r => #name r = f) results)) must_prove
  in
    map (fn f => suite ^ "." ^ f) (map #name (List.filter failed results) @ missing)
  end

val () =
  case List.concat (map run suites) of
    [] => ()
  | bad => raise mk_HOL_ERR "solidityTranslatorCorpus" "run"
                   ("failed, not proved, or slower than the cap: " ^
                    String.concatWith ", " bad)
