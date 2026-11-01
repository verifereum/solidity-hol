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

fun word_term bits i =
  if 0 <= i andalso i < IntInf.pow (2, bits) then
    wordsSyntax.mk_wordi (Arbnum.fromString (IntInf.toString i), bits)
  else fail ("not a " ^ Int.toString bits ^ "-bit word: " ^ IntInf.toString i)

(* Calldata as 0x hex, a named function and its arguments, or a creation
 * ("deploy": true) from the suite's initcode with constructor arguments. *)
fun call_input initcode c =
  case (JSONUtil.findField c "calldata", JSONUtil.findField c "function",
        JSONUtil.findField c "deploy") of
    (SOME (JSON.STRING s), NONE, NONE) => con "RawCall" [bytes_term (hex_bytes s)]
  | (NONE, SOME (JSON.STRING f), NONE) =>
      con "NamedCall"
        [stringSyntax.fromMLstring f, arguments (array_field c "args")]
  | (NONE, NONE, SOME (JSON.BOOL true)) =>
      con "Deploy" [initcode (), arguments (array_field c "args")]
  | _ => fail "a case has either calldata, a function and its arguments, \
              \or deploy and the constructor's arguments"

(* Logs as a list of {"logger": address, "topics": [...], "data": "0x..."},
 * the logger the contract by default. *)
fun logs v =
  let
    val bytes32 = wordsSyntax.mk_int_word_type 256
    fun log l =
      pairSyntax.list_mk_pair
        [word_term 160 (case JSONUtil.findField l "logger" of
                          SOME a => integer a
                        | NONE => 0x1000),
         listSyntax.mk_list
           (map (word_term 256 o integer) (array_field l "topics"), bytes32),
         bytes_term (hex_bytes (string_field l "data"))]
  in
    listSyntax.mk_list
      (map log (case v of NONE => [] | SOME (JSON.ARRAY ls) => ls
                        | SOME _ => fail "logs is a list"),
       pairSyntax.list_mk_prod
         [wordsSyntax.mk_int_word_type 160, listSyntax.mk_list_type bytes32,
          listSyntax.mk_list_type byte_ty])
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

fun logs_json tm =
  json_array
    (map (fn e =>
            let val (_, fields) = TypeBase.dest_record e in
              json_object
                [("logger", json_string ("0x" ^ String.map Char.toLower
                    (Arbnum.toHexString
                       (wordsSyntax.dest_word_literal (Lib.assoc "logger" fields))))),
                 ("topics", json_array
                    (map (fn t => json_string ("0x" ^ String.map Char.toLower
                                    (Arbnum.toHexString (wordsSyntax.dest_word_literal t))))
                       (fst (listSyntax.dest_list
                               (Lib.assoc "topics" fields))))),
                 ("data", json_string (hex_of_bytes (Lib.assoc "data" fields)))]
            end)
         (fst (listSyntax.dest_list tm)))

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

fun prepared_constants prefix (prepared : solidityPrepareLib.prepared) =
  let
    val unit_def = define (prefix ^ "_unit") (#unit prepared)
    val () = cv_auto_trans unit_def
    val program_def = define (prefix ^ "_program") (#program prepared)
    val () = cv_auto_trans program_def
    fun named name th = save_thm (prefix ^ name,
      REWRITE_RULE [SYM unit_def, SYM program_def] th)
    val _ = named "_source_valid" (#source_valid prepared)
    val _ = named "_elaborates" (#elaborates prepared)
    val _ = named "_program_wf" (#core_wf prepared)
  in
    (lhs (concl unit_def), lhs (concl program_def))
  end

fun code_definition name hex =
  let
    val def = define name
                “REVERSE $ hex_to_rev_bytes [] ^(stringSyntax.fromMLstring hex)”
    val () = cv_trans_deep_embedding EVAL def
  in
    lhs (concl def)
  end

(* The deployed code ("deployedBytecode") or initcode ("bytecode"). *)
fun code_constant name kind artifact source contract =
  let
    val hex = JSONUtil.asString (JSONUtil.get (artifact,
      map JSONUtil.SEL ["output", "contracts", source, contract, "evm",
                        kind, "object"]))
      handle e as JSONUtil.JSONError _ => fail (JSONUtil.exnMessage e)
           | e as JSONUtil.FieldNotFound _ => fail (JSONUtil.exnMessage e)
  in
    code_definition name hex
  end

(* The peer's code, from its own artifact; no code without a peer. *)
fun peer_code root prefix s =
  case JSONUtil.findField s "peer" of
    NONE => listSyntax.mk_nil byte_ty
  | SOME p =>
      code_definition (prefix ^ "_peer_code")
        (solidityImportLib.artifact_deployed_bytecode
           (root ^ "/" ^ string_field p "artifact") (string_field p "source")
           (string_field p "contract"))
      handle solidityImportLib.ImportError msg => fail msg

(* Cases *)

fun is_con name tm =
  let val f = fst (strip_comb tm) in
    is_const f andalso fst (dest_const f) = name
  end

fun run_case {suite, code, initcode, peer, unit, program, fuel} c =
  let
    val case_name = name_field c "name"
    val theorem = suite ^ "_" ^ case_name
    val fuel = case JSONUtil.findField c "fuel" of
                 SOME v => integer v
               | NONE => fuel
    val input = call_input initcode c
    val expect = expectation (field c "expect")
    val case_tm = TypeBase.mk_record
      (mk_thy_type {Thy = "solidityDifferential", Tyop = "differential_case",
                    Args = []},
       [("case_sender",
         word_term 160 (case JSONUtil.findField c "sender" of
                          SOME v => integer v
                        | NONE => 0x2000)),
        ("case_value",
         num_term (case JSONUtil.findField c "value" of
                     SOME v => integer v
                   | NONE => 0)),
        ("case_input", input),
        ("case_storage", storage (JSONUtil.findField c "storage")),
        ("case_peer_code", peer),
        ("case_peer_storage", storage (JSONUtil.findField c "peer_storage")),
        ("case_expect", expect),
        ("case_final", storage (JSONUtil.findField c "final_storage")),
        ("case_logs", logs (JSONUtil.findField c "logs"))])
    val verdict_tm =
      list_mk_comb (prim_mk_const {Thy = "solidityDifferential",
                                   Name = "differential_verdict"},
                    [code, unit, program, num_term fuel, case_tm])
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
    else if is_con "LogMismatch" result orelse is_con "LogUnexpected" result then
      let
        val mismatch = is_con "LogMismatch" result
        val (bytecode, other) =
          case snd (strip_comb result) of
            [b, x] => (b, x)
          | _ => raise ERR "run_case" "unexpected verdict"
      in
        emit (base @ [("status", json_string (if mismatch then "log-mismatch"
                                              else "log-unexpected")),
                      ("bytecode_logs", logs_json bytecode),
                      (if mismatch then "source_logs" else "expected_logs",
                       logs_json other)]);
        false
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
                                        [unit, input, expect]))))
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
    let
      val checked = solidityPrepareLib.prepare_artifact
        {root = root, path = artifact, source = source}
      (* The importer keeps the one contract no other inherits; the bytecode
       * compared must be that contract's. *)
      fun record_field name tm = Lib.assoc name (snd (TypeBase.dest_record tm))
      val names =
        map (stringSyntax.fromHOLstring o record_field "contract_name")
          (fst (listSyntax.dest_list
                  (record_field "unit_contracts" (#unit (#prepared checked)))))
      val () =
        if names = [contract] then ()
        else fail ("the unit's contracts are [" ^ String.concatWith ", " names ^
                   "], not " ^ contract)
      val (unit, program) = prepared_constants prefix (#prepared checked)
      val code = code_constant (prefix ^ "_code") "deployedBytecode"
                   (#artifact checked) source contract
      (* Defined once, by the suite's first creation case. *)
      val initcode_constant = ref NONE
      fun initcode () =
        case !initcode_constant of
          SOME tm => tm
        | NONE =>
            let val tm = code_constant (prefix ^ "_initcode") "bytecode"
                           (#artifact checked) source contract
            in initcode_constant := SOME tm; tm end
      val peer = peer_code root prefix s
      val () = emit [("kind", json_string "suite"),
                     ("suite", json_string suite),
                     ("status", json_string "ok"),
                     ("theorems", json_array (map json_string
                       [prefix ^ "_elaborates", prefix ^ "_program_wf"]))]
      val env = {suite = suite, code = code, initcode = initcode, peer = peer,
                 unit = unit, program = program, fuel = fuel}
    in
      List.foldl (fn (c, ok) => run_case env c andalso ok) true cases
    end
  end
  handle solidityPrepareLib.PreparationError (kind, message) =>
           suite_failure (string_field s "name" handle _ => "?")
             (solidityPrepareLib.failure_name kind) message
       | CorpusError msg => suite_failure (string_field s "name" handle _ => "?")
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
