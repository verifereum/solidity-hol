(* Run by tools/semantic_tests_coverage.py under `holbuild run`. Imports and
 * elaborates every test listed in the file named by SEMANTIC_TESTS_MANIFEST,
 * one "name<TAB>path" line per test, where path holds a JSON object of the
 * test's ASTs by source name. Prints one coverage-result line per test.
 *)
load "solidityImportLib";
load "solidityElaborateTheory";
load "cv_transLib";

local
  open HolKernel boolLib

  fun json_string s =
    let
      fun escape #"\"" = "\\\""
        | escape #"\\" = "\\\\"
        | escape c =
            if Char.isPrint c then String.str c
            else "\\u" ^ StringCvt.padLeft #"0" 4 (Int.fmt StringCvt.HEX (ord c))
    in
      "\"" ^ String.translate escape s ^ "\""
    end

  fun emit test status message =
    (print ("coverage-result: {\"test\":" ^ json_string test ^
            ",\"status\":" ^ json_string status ^
            (case message of
               NONE => ""
             | SOME m => ",\"message\":" ^ json_string m) ^ "}\n");
     TextIO.flushOut TextIO.stdOut)

  val elaborate_unit_tm =
    prim_mk_const {Thy = "solidityElaborate", Name = "elaborate_unit"}

  fun elaborates unit =
    optionSyntax.is_some
      (rhs (concl (cv_transLib.cv_eval (mk_comb (elaborate_unit_tm, unit)))))

  (* Every source unit must import before any is elaborated, so that the
   * first rejection reported is the importer's when there is one.
   *)
  fun run_test test path =
    case JSONParser.parseFile path of
      JSON.OBJECT sources =>
        (case SOME (map (solidityImportLib.import_source_unit o snd) sources)
              handle solidityImportLib.ImportError msg =>
                (emit test "import-rejected" (SOME msg); NONE) of
           NONE => ()
         | SOME units =>
             case List.find (not o elaborates o snd)
                    (ListPair.zip (map fst sources, units)) of
               NONE => emit test "admitted" NONE
             | SOME (source, _) =>
                 emit test "elaboration-rejected"
                   (SOME ("elaborate_unit returned NONE for " ^ source)))
    | _ => raise Fail (path ^ ": expected an object of ASTs")

  val manifest =
    case OS.Process.getEnv "SEMANTIC_TESTS_MANIFEST" of
      SOME m => m
    | NONE => raise Fail "SEMANTIC_TESTS_MANIFEST is not set"

  fun lines stream =
    case TextIO.inputLine stream of
      NONE => []
    | SOME l => String.substring (l, 0, size l - 1) :: lines stream
in
  val () =
    List.app
      (fn line =>
         case String.fields (fn c => c = #"\t") line of
           [test, path] => run_test test path
         | _ => raise Fail ("malformed manifest line " ^ line))
      (lines (TextIO.openIn manifest))
end;
