(* Run by tools/semantic_tests_coverage.py under `holbuild run`. Checks the
 * preparation of every test in SEMANTIC_TESTS_MANIFEST: one "name<TAB>path"
 * line per test, where path holds the complete compiler artifact. Prints one
 * coverage-result line per test.
 *)
load "wordsLib";
load "solidityPrepareLib";

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

  fun run_test test path =
    let
      val artifact = solidityPrepareLib.read_artifact {root = ".", path = path}
      val sources = case JSONUtil.lookupField
        (JSONUtil.lookupField artifact "output") "sources" of
          JSON.OBJECT sources => map fst sources
        | _ => raise Fail (path ^ ": expected output sources object")
      val () = if null sources then
        raise solidityPrepareLib.PreparationError
          (solidityPrepareLib.UnsupportedLowering, "artifact has no source units")
        else ()
      val _ = map (fn source => solidityPrepareLib.prepare_artifact
        {root = ".", path = path, source = source}) sources
    in
      emit test "admitted" NONE
    end
    handle solidityPrepareLib.PreparationError (kind, message) =>
      let val status = case kind of
        solidityPrepareLib.UnsupportedImport => "import-rejected"
      | solidityPrepareLib.UnsupportedLowering => "elaboration-rejected"
      | solidityPrepareLib.SourceRejected => "elaboration-rejected"
      | _ => solidityPrepareLib.failure_name kind
      in emit test status (SOME message) end

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
