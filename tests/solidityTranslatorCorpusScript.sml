(* The core-to-HOL translator on every function of the differential corpus
 * (testdata/differential/corpus.json). Each function must translate and
 * prove, or be one the translator does not cover yet; any other failure, or
 * a proof slower than max_seconds, fails the build after every suite has run. Prints one
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
    ("doubleUntil", WF_REL_TAC ‘measure (λ(n, k). n - k)’ >> rw[uint_add_def])])]

fun json_string s = "\"" ^ String.toCString s ^ "\""

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
    fun failed {outcome = Failed _, ...} = true
      | failed {seconds, ...} = seconds > max_seconds
  in
    map #name (List.filter failed results)
  end

val () =
  case List.concat (map run ["pure_core", "scalars", "control", "calls",
                             "storage", "mappings"]) of
    [] => ()
  | bad => raise mk_HOL_ERR "solidityTranslatorCorpus" "run"
                   ("failed or slower than the cap: " ^ String.concatWith ", " bad)
