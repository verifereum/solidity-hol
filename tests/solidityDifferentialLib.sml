structure solidityDifferentialLib :> solidityDifferentialLib =
struct

open HolKernel boolLib bossLib solidityDifferentialTheory cv_transLib intLib wordsLib

val ERR = mk_HOL_ERR "solidityDifferentialLib"

exception CorpusError of string

fun fail msg = raise CorpusError msg

(* Result lines, read by tools/run_differential.py *)

fun json_string s =
  let
    fun escape #"\"" = "\\\""
      | escape #"\\" = "\\\\"
      | escape #"\n" = "\\n"
      | escape c =
          if Char.isPrint c then String.str c
          else "\\u" ^ StringCvt.padLeft #"0" 4 (Int.fmt StringCvt.HEX (ord c))
  in
    "\"" ^ String.translate escape s ^ "\""
  end

fun json_object fields =
  "{" ^ String.concatWith ","
          (map (fn (k, v) => json_string k ^ ":" ^ v) fields) ^ "}"

fun json_array vs = "[" ^ String.concatWith "," vs ^ "]"

fun emit fields = print ("differential-result: " ^ json_object fields ^ "\n")

(* Corpus input *)

val field = JSONUtil.lookupField
fun string_field v k = JSONUtil.asString (field v k)
fun array_field v k = Vector.foldr (op ::) [] (JSONUtil.asArray (field v k))

fun identifier s =
  size s > 0 andalso Char.isAlpha (String.sub (s, 0)) andalso
  CharVector.all (fn c => Char.isAlphaNum c orelse c = #"_") s

fun name_field v k =
  let val s = string_field v k in
    if identifier s then s else fail ("not an identifier: " ^ s)
  end

fun hex_digit c =
  if Char.isDigit c then ord c - ord #"0"
  else if #"a" <= c andalso c <= #"f" then ord c - ord #"a" + 10
  else if #"A" <= c andalso c <= #"F" then ord c - ord #"A" + 10
  else fail ("not a hex digit: " ^ String.str c)

(* "0x" followed by an even number of hex digits *)
fun hex_bytes s =
  let
    val digits =
      if String.isPrefix "0x" s then String.extract (s, 2, NONE)
      else fail ("expected 0x-prefixed hex: " ^ s)
    fun go [] = []
      | go (h :: l :: rest) = (16 * hex_digit h + hex_digit l) :: go rest
      | go [_] = fail ("odd number of hex digits: " ^ s)
  in
    go (explode digits)
  end

fun is_hex s = String.isPrefix "0x" s

fun decimal s =
  let
    val (negative, digits) =
      if String.isPrefix "-" s then (true, String.extract (s, 1, NONE))
      else (false, s)
  in
    if size digits > 0 andalso CharVector.all Char.isDigit digits then
      (if negative then ~1 else 1) * valOf (IntInf.fromString digits)
    else fail ("not an integer: " ^ s)
  end

fun integer (JSON.INT i) = i
  | integer (JSON.STRING s) =
      if is_hex s then
        List.foldl (fn (b, acc) => acc * 256 + IntInf.fromInt b) 0 (hex_bytes s)
      else decimal s
  | integer _ = fail "expected an integer"

(* Terms *)

fun con name args =
  list_mk_comb (prim_mk_const {Thy = "solidityDifferential", Name = name}, args)

fun num_term i = numSyntax.mk_numeral (Arbnum.fromString (IntInf.toString i))

fun int_term i =
  if i < 0 then intSyntax.mk_negated (intSyntax.mk_injected (num_term (~i)))
  else intSyntax.mk_injected (num_term i)

val byte_ty = wordsSyntax.mk_int_word_type 8

fun bytes_term bs =
  listSyntax.mk_list (map (fn b => wordsSyntax.mk_wordii (b, 8)) bs, byte_ty)

val argument_ty =
  mk_thy_type {Thy = "solidityDifferential", Tyop = "argument", Args = []}

fun argument (JSON.BOOL b) = con "BoolArg" [if b then T else F]
  | argument (JSON.INT i) = con "IntArg" [int_term i]
  | argument (JSON.STRING s) =
      if is_hex s then con "BytesArg" [bytes_term (hex_bytes s)]
      else con "IntArg" [int_term (decimal s)]
  | argument _ = fail "an argument is an integer, a boolean or a 0x string"

fun arguments vs = listSyntax.mk_list (map argument vs, argument_ty)

fun expectation v =
  case v of
    JSON.OBJECT [("return", JSON.ARRAY vs)] => con "ExpectReturn" [arguments vs]
  | JSON.OBJECT [("panic", code)] => con "ExpectPanic" [num_term (integer code)]
  | JSON.OBJECT [("revert", JSON.STRING s)] =>
      con "ExpectRevert" [bytes_term (hex_bytes s)]
  | _ => fail "expect is one of {\"return\": [...]}, {\"panic\": code}, \
              \{\"revert\": \"0x...\"}"

(* An object from slot to value, both 256-bit words. *)
fun storage v =
  let
    fun word i =
      if 0 <= i andalso i < IntInf.pow (2, 256) then num_term i
      else fail ("not a 256-bit word: " ^ IntInf.toString i)
    fun entry (k, x) = pairSyntax.mk_pair (word (integer (JSON.STRING k)), word (integer x))
  in
    case v of
      NONE => listSyntax.mk_list ([], “:num # num”)
    | SOME (JSON.OBJECT kvs) => listSyntax.mk_list (map entry kvs, “:num # num”)
    | SOME _ => fail "storage is an object from slot to value"
  end

(* Outcomes as JSON *)

fun hex_of_bytes tm =
  "0x" ^ String.concat
    (map (fn b =>
            StringCvt.padLeft #"0" 2
              (String.map Char.toLower
                 (Arbnum.toHexString (wordsSyntax.dest_word_literal b))))
         (fst (listSyntax.dest_list tm)))

fun outcome_json tm =
  let val (f, args) = strip_comb tm in
    case (fst (dest_const f), args) of
      ("Returned", [bs]) => json_object [("returned", json_string (hex_of_bytes bs))]
    | ("Reverted", [bs]) => json_object [("reverted", json_string (hex_of_bytes bs))]
    | ("Diagnostic", [d]) =>
        json_object [("diagnostic", json_string (fst (dest_const d)))]
    | _ => json_string (term_to_string tm)
  end

fun storage_json tm =
  json_object
    (map (fn p =>
            let val (k, v) = pairSyntax.dest_pair p in
              (Arbnum.toString (numSyntax.dest_numeral k),
               json_string ("0x" ^ String.map Char.toLower
                                     (Arbnum.toHexString (numSyntax.dest_numeral v))))
            end)
         (fst (listSyntax.dest_list tm)))

(* Definitions made by the corpus *)

fun define name tm =
  new_definition (name ^ "_def", mk_eq (mk_var (name, type_of tm), tm))

val elaborate_unit_tm = prim_mk_const {Thy = "solidityElaborate", Name = "elaborate_unit"}

fun unit_constant prefix artifact source =
  let
    val def = define (prefix ^ "_unit")
                (solidityImportLib.import_artifact artifact source)
    val () = cv_auto_trans def
  in
    lhs (concl def)
  end

fun code_constant prefix artifact source contract =
  let
    val hex = solidityImportLib.artifact_deployed_bytecode artifact source contract
    val def = define (prefix ^ "_code")
                “REVERSE $ hex_to_rev_bytes [] ^(stringSyntax.fromMLstring hex)”
    val () = cv_trans_deep_embedding EVAL def
  in
    lhs (concl def)
  end

(* The elaborated program, or NONE if elaboration rejects the unit. *)
fun program_constant prefix unit =
  let
    val elaborated = cv_eval (mk_comb (elaborate_unit_tm, unit))
    val result = rhs (concl elaborated)
  in
    if optionSyntax.is_none result then NONE
    else
      let
        val def = define (prefix ^ "_program") (optionSyntax.dest_some result)
        val () = cv_auto_trans def
        val th = CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (SYM def)))) elaborated
      in
        SOME (lhs (concl def), def, save_thm (prefix ^ "_elaborates", th))
      end
  end

fun program_wf prefix program def =
  let
    val th = (PURE_REWRITE_CONV [def] THENC EVAL)
               “wf_core_program (core_program_environment [] ^program) ^program”
  in
    if rhs (concl th) ~~ T then
      SOME (save_thm (prefix ^ "_program_wf",
                      EQT_ELIM (CONV_RULE (LAND_CONV (REWRITE_CONV [SYM def])) th)))
    else NONE
  end
  handle HOL_ERR _ => NONE

(* Cases *)

fun is_con name tm =
  let val f = fst (strip_comb tm) in
    is_const f andalso fst (dest_const f) = name
  end

fun run_case {suite, code, unit, program, fuel} c =
  let
    val case_name = name_field c "name"
    val theorem = suite ^ "_" ^ case_name
    val function = string_field c "function"
    val fuel = case JSONUtil.findField c "fuel" of
                 SOME v => integer v
               | NONE => fuel
    val args = arguments (array_field c "args")
    val initial = storage (JSONUtil.findField c "storage")
    val expect = expectation (field c "expect")
    val final = storage (JSONUtil.findField c "final_storage")
    val verdict_tm =
      list_mk_comb (prim_mk_const {Thy = "solidityDifferential",
                                   Name = "differential_verdict"},
                    [code, unit, program, num_term fuel,
                     stringSyntax.fromMLstring function, args, initial, expect,
                     final])
    val verdict = cv_eval verdict_tm
    val result = rhs (concl verdict)
    val base = [("kind", json_string "case"), ("suite", json_string suite),
                ("case", json_string case_name)]
  in
    if is_con "Agree" result then
      let
        val agrees_tm = list_mk_comb (prim_mk_const {Thy = "solidityDifferential",
                                                     Name = "differential_agrees"},
                                      snd (strip_comb verdict_tm))
        val th = EQT_ELIM ((PURE_REWRITE_CONV [differential_agrees_def, verdict]
                            THENC REWRITE_CONV [is_agreement_def]) agrees_tm)
        val _ = save_thm (theorem, th)
      in
        emit (base @ [("status", json_string "agree"),
                      ("theorem", json_string theorem),
                      ("outcome", outcome_json (rand result))]);
        true
      end
    else if is_con "StorageMismatch" result orelse is_con "StorageUnexpected" result
    then
      let
        (* a mismatch carries the source's storage, an unexpected result the
         * expected one; in the latter both runs ended with the first *)
        val mismatch = is_con "StorageMismatch" result
        val (bytecode, other) =
          case snd (strip_comb result) of
            [b, x] => (b, x)
          | _ => raise ERR "run_case" "unexpected verdict"
      in
        emit (base @ [("message", json_string
                        "Complete storage is compared; displayed values cover the listed slots."),
                      ("status", json_string (if mismatch then "storage-mismatch"
                                              else "storage-unexpected")),
                      ("bytecode_storage", storage_json bytecode),
                      (if mismatch then "source_storage" else "expected_storage",
                       storage_json other)]);
        false
      end
    else
      let
        val expected = rhs (concl (cv_eval
                         (list_mk_comb (prim_mk_const {Thy = "solidityDifferential",
                                                       Name = "expected_outcome"},
                                        [unit, stringSyntax.fromMLstring function,
                                         expect]))))
        val (kind, args) = strip_comb result
        val (bytecode, source) =
          case (fst (dest_const kind), args) of
            ("Unexpected", [agreed, _]) => (agreed, agreed)
          | (_, [b, s]) => (b, s)
          | _ => raise ERR "run_case" "unexpected verdict"
      in
        emit (base @ [("status", json_string (String.map Char.toLower
                                                (fst (dest_const kind)))),
                      ("bytecode", outcome_json bytecode),
                      ("source", outcome_json source),
                      ("expected", outcome_json expected)]);
        false
      end
  end
  handle e =>
    (emit [("kind", json_string "case"), ("suite", json_string suite),
           ("case", json_string (string_field c "name" handle _ => "?")),
           ("status", json_string "error"),
           ("message", json_string (General.exnMessage e))];
     false)

(* Suites *)

fun suite_failure suite status message =
  (emit [("kind", json_string "suite"), ("suite", json_string suite),
         ("status", json_string status), ("message", json_string message)];
   false)

fun run_suite root fuel s =
  let
    val suite = name_field s "name"
    val prefix = "corpus_" ^ suite
    val artifact = root ^ "/" ^ string_field s "artifact"
    val source = string_field s "source"
    val contract = string_field s "contract"
    val cases = array_field s "cases"
  in
    case (SOME (unit_constant prefix artifact source)
          handle solidityImportLib.ImportError msg =>
            (suite_failure suite "import-rejected" msg; NONE)) of
      NONE => false
    | SOME unit =>
      case program_constant prefix unit of
        NONE => suite_failure suite "elaboration-rejected"
                  "elaborate_unit returned NONE"
      | SOME (program, def, _) =>
        case program_wf prefix program def of
          NONE => suite_failure suite "invalid-core"
                    "wf_core_program does not hold"
        | SOME _ =>
          let
            val code = code_constant prefix artifact source contract
            val () = emit [("kind", json_string "suite"),
                           ("suite", json_string suite),
                           ("status", json_string "ok"),
                           ("theorems",
                            json_array (map json_string
                              [prefix ^ "_elaborates", prefix ^ "_program_wf"]))]
            val env = {suite = suite, code = code, unit = unit,
                       program = program, fuel = fuel}
          in
            List.foldl (fn (c, ok) => run_case env c andalso ok) true cases
          end
  end
  handle CorpusError msg => suite_failure (string_field s "name" handle _ => "?")
                              "error" msg
       | e as HOL_ERR _ => suite_failure (string_field s "name" handle _ => "?")
                             "error" (General.exnMessage e)

fun run_corpus {root, corpus} =
  let
    val path = root ^ "/" ^ corpus
    val v = JSONParser.parseFile path
    val () = if string_field v "format" = "solidity-hol-differential-corpus-v1"
             then () else raise ERR "run_corpus" (path ^ ": unsupported format")
    val fuel = integer (field v "fuel")
    val ok = List.foldl (fn (s, ok) => run_suite root fuel s andalso ok) true
               (array_field v "suites")
  in
    if ok then ()
    else raise ERR "run_corpus" "differential corpus failed; see the \
                                \differential-result lines"
  end
  handle CorpusError msg => raise ERR "run_corpus" msg

end
