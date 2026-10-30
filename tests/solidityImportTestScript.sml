(* Import of the pinned compiler's AST for testdata/frontend/pure_core.sol and
 * testdata/differential/storage.sol, and negative fixtures derived from them
 * by single edits to the JSON.
 *)
Theory solidityImportTest
Ancestors
  solidityImport
Libs
  solidityImportLib cv_transLib intLib

(* Read by holbuild's dependency scanner, which stages the fixture. *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [
  "../testdata/frontend/expected/pure_core.json",
  "../testdata/differential/expected/storage.json"
]

val fixture = "../testdata/frontend/expected/pure_core.json"
val source = "testdata/frontend/pure_core.sol"

Definition pure_core_def:
  pure_core = ^(import_artifact fixture source)
End

val () = cv_auto_trans pure_core_def;

Theorem pure_core_valid:
  valid_src_unit pure_core
Proof
  CONV_TAC cv_eval
QED

Theorem pure_core_signatures:
  MAP (λf. (f.fn_name, OPT_MMAP variable_type f.fn_parameters,
            OPT_MMAP variable_type f.fn_returns))
    (HD pure_core.unit_contracts).contract_functions =
  [("add", SOME [UintT 8; UintT 8], SOME [UintT 8]);
   ("wrappingAdd", SOME [UintT 8; UintT 8], SOME [UintT 8]);
   ("count", SOME [UintT 256], SOME [UintT 256; UintT 256]);
   ("sum", SOME [UintT 256], SOME [UintT 256]);
   ("doubleUntil", SOME [UintT 256], SOME [UintT 256]);
   ("fact", SOME [UintT 256], SOME [UintT 256]);
   ("divmod", SOME [UintT 256; UintT 256], SOME [UintT 256; UintT 256]);
   ("swap", SOME [], SOME [UintT 256; UintT 256]);
   ("locals", SOME [UintT 256], SOME [UintT 256]);
   ("narrow", SOME [UintT 256], SOME [UintT 8; BoolT]);
   ("negate", SOME [IntT 8], SOME [IntT 8]);
   ("identity", SOME [AddressT NonpayableAddress; FixedBytesT 4],
    SOME [AddressT NonpayableAddress; FixedBytesT 4]);
   ("guardedDivide", SOME [UintT 256], SOME [BoolT]);
   ("badDivide", SOME [UintT 256], SOME [BoolT]);
   ("shortCircuit", SOME [UintT 256], SOME [BoolT; UintT 256]);
   ("panicOrder", SOME [UintT 256], SOME [UintT 256]);
   ("argumentOrder", SOME [UintT 256], SOME [UintT 256; UintT 256]);
   ("compoundOrder", SOME [UintT 256], SOME [UintT 256])]
Proof
  EVAL_TAC
QED

Theorem type_name_normalization:
  normalize_type_name (SrcElementaryTypeName i "uint" NONE) =
    SOME (UintT 256) ∧
  normalize_type_name (SrcElementaryTypeName i "uint7" NONE) = NONE ∧
  normalize_type_name (SrcElementaryTypeName i "bytes33" NONE) = NONE ∧
  normalize_type_name (SrcElementaryTypeName i "bytes" NONE) = NONE ∧
  normalize_type_name (SrcElementaryTypeName i "string" NONE) = NONE ∧
  normalize_type_name (SrcElementaryTypeName i "address" (SOME "payable")) =
    SOME (AddressT PayableAddress) ∧
  normalize_type_name (SrcElementaryTypeName i "address" NONE) = NONE ∧
  normalize_type_name (SrcElementaryTypeName i "bool" (SOME "payable")) = NONE
Proof
  EVAL_TAC
QED

Theorem type_identifier_decoding:
  decode_type_identifier "t_rational_minus_7_by_2" =
    SOME (SrcRational (-7) 2) ∧
  decode_type_identifier "t_rational_1_by_0" = NONE ∧
  decode_type_identifier "t_tuple$_t_uint256_$_t_bool_$" =
    SOME (SrcTupleType [UintT 256; BoolT]) ∧
  decode_type_identifier "t_tuple$__$" = SOME (SrcTupleType []) ∧
  decode_type_identifier "t_address_payable" =
    SOME (SrcType (AddressT PayableAddress)) ∧
  decode_type_identifier "t_uint7" = NONE ∧
  decode_type_identifier "t_uint" = NONE ∧
  decode_type_identifier "t_string_memory_ptr" = NONE ∧
  decode_type_identifier "t_bytes_memory_ptr" = NONE
Proof
  EVAL_TAC
QED

(* Negative fixtures: the fixture's AST with one edit to the first node, in
 * document order, of a given nodeType.
 *)

fun artifact_part path keys =
  JSONUtil.get (JSONParser.parseFile path,
    [JSONUtil.SEL "output"] @ map JSONUtil.SEL keys)

val ast = artifact_part fixture ["sources", source, "ast"]
val contracts = artifact_part fixture ["contracts", source]

fun is_node ty =
  JSONUtil.testField "nodeType" (fn JSON.STRING s => s = ty | _ => false)

fun edit_first ty f v =
  let
    val edited = ref false
    fun go v =
      if !edited then v
      else case v of
             JSON.OBJECT kvs =>
               if is_node ty v then (edited := true; f v)
               else JSON.OBJECT (map (fn (k, x) => (k, go x)) kvs)
           | JSON.ARRAY vs => JSON.ARRAY (map go vs)
           | _ => v
    val result = go v
  in
    if !edited then result else raise Fail ("no " ^ ty ^ " node")
  end

fun set_field k x (JSON.OBJECT kvs) =
      JSON.OBJECT (map (fn (k', y) => if k' = k then (k', x) else (k', y)) kvs)
  | set_field _ _ v = v

fun drop_field k (JSON.OBJECT kvs) =
      JSON.OBJECT (List.filter (fn (k', _) => k' <> k) kvs)
  | drop_field _ v = v

fun type_identifier tid =
  set_field "typeDescriptions"
    (JSON.OBJECT [("typeIdentifier", JSON.STRING tid),
                  ("typeString", JSON.STRING "")])

fun import_error_with contracts name v =
  (import_source_unit v contracts; raise Fail (name ^ ": imported"))
  handle ImportError _ => ()

val import_error = import_error_with contracts

(* An edited unit that imports, as a cv-translated constant. *)
fun edited_unit_with contracts name v =
  let
    val tm = import_source_unit v contracts
    val def = new_definition (name ^ "_def", mk_eq (mk_var (name, type_of tm), tm))
  in
    cv_auto_trans def
  end

val edited_unit = edited_unit_with contracts

(* Unknown forms, missing annotations and unsupported features fail import. *)

val () = import_error "unknown statement"
  (edit_first "Break" (set_field "nodeType" (JSON.STRING "InlineAssembly")) ast)
val () = import_error "unknown expression"
  (edit_first "Literal" (set_field "nodeType" (JSON.STRING "Conditional")) ast)
val () = import_error "missing type annotation"
  (edit_first "Identifier" (drop_field "typeDescriptions") ast)
val () = import_error "missing declaration reference"
  (edit_first "Identifier" (drop_field "referencedDeclaration") ast)
val () = import_error "missing common type"
  (edit_first "BinaryOperation" (drop_field "commonType") ast)
val () = import_error "function as state variable"
  (edit_first "FunctionDefinition"
     (set_field "nodeType" (JSON.STRING "VariableDeclaration")) ast)
val () = import_error "modifier"
  (edit_first "FunctionDefinition"
     (set_field "modifiers" (JSON.ARRAY [JSON.OBJECT []])) ast)
val () = import_error "named arguments"
  (edit_first "FunctionCall"
     (set_field "names" (JSON.ARRAY [JSON.STRING "n"])) ast)
val () = import_error "inheritance"
  (edit_first "ContractDefinition"
     (set_field "linearizedBaseContracts" (JSON.ARRAY [])) ast)

(* Duplicate and dangling ids and inconsistent types import but are invalid. *)

val unit_id = JSONUtil.lookupField ast "id"

val () = edited_unit "duplicate_id"
  (edit_first "Literal" (set_field "id" unit_id) ast)

val () = edited_unit "dangling_reference"
  (edit_first "Identifier"
     (set_field "referencedDeclaration" (JSON.INT 999999)) ast)

(* The first identifier is the uint8 parameter x of add. *)
val () = edited_unit "identifier_type_mismatch"
  (edit_first "Identifier" (type_identifier "t_uint256") ast)

(* A reference to the function add used as a value. *)
val add_id =
  JSONUtil.get (ast, [JSONUtil.SEL "nodes", JSONUtil.SUB 1,
                      JSONUtil.SEL "nodes", JSONUtil.SUB 0, JSONUtil.SEL "id"])

val () = edited_unit "function_as_value"
  (edit_first "Identifier" (set_field "referencedDeclaration" add_id) ast)

val () = edited_unit "declaration_type_mismatch"
  (edit_first "VariableDeclaration" (type_identifier "t_bool") ast)

val () = edited_unit "wrong_scope"
  (edit_first "VariableDeclaration" (set_field "scope" (JSON.INT 999999)) ast)

val () = edited_unit "unlinked_declaration"
  (edit_first "VariableDeclarationStatement"
     (set_field "assignments" (JSON.ARRAY [JSON.NULL])) ast)

(* The first call is fact(n - 1). *)
val () = edited_unit "call_arity"
  (edit_first "FunctionCall" (set_field "arguments" (JSON.ARRAY [])) ast)

Theorem duplicate_id_rejected:
  ¬valid_src_unit duplicate_id
Proof
  CONV_TAC cv_eval
QED

Theorem dangling_reference_rejected:
  ¬valid_src_unit dangling_reference
Proof
  CONV_TAC cv_eval
QED

Theorem identifier_type_mismatch_rejected:
  ¬valid_src_unit identifier_type_mismatch
Proof
  CONV_TAC cv_eval
QED

Theorem function_as_value_rejected:
  ¬valid_src_unit function_as_value
Proof
  CONV_TAC cv_eval
QED

Theorem declaration_type_mismatch_rejected:
  ¬valid_src_unit declaration_type_mismatch
Proof
  CONV_TAC cv_eval
QED

Theorem wrong_scope_rejected:
  ¬valid_src_unit wrong_scope
Proof
  CONV_TAC cv_eval
QED

Theorem unlinked_declaration_rejected:
  ¬valid_src_unit unlinked_declaration
Proof
  CONV_TAC cv_eval
QED

Theorem call_arity_rejected:
  ¬valid_src_unit call_arity
Proof
  CONV_TAC cv_eval
QED

(* State variables and the storage layout *)

val storage_fixture = "../testdata/differential/expected/storage.json"
val storage_source = "testdata/differential/storage.sol"

Definition storage_unit_def:
  storage_unit = ^(import_artifact storage_fixture storage_source)
End

val () = cv_auto_trans storage_unit_def;

Theorem storage_unit_valid:
  valid_src_unit storage_unit
Proof
  CONV_TAC cv_eval
QED

Theorem storage_unit_layout:
  MAP (λe. (e.storage_slot, e.storage_offset, e.storage_type_id))
    (HD storage_unit.unit_contracts).contract_storage =
  [(0, 0, "t_uint256"); (1, 0, "t_uint8"); (1, 1, "t_int16");
   (1, 3, "t_bool"); (1, 4, "t_address"); (1, 24, "t_bytes4");
   (2, 0, "t_uint128"); (2, 16, "t_uint128"); (3, 0, "t_int256")]
Proof
  EVAL_TAC
QED

val storage_ast =
  artifact_part storage_fixture ["sources", storage_source, "ast"]
val storage_contracts =
  artifact_part storage_fixture ["contracts", storage_source]

(* The first variable declaration is the state variable total. *)
val () = import_error_with storage_contracts "public state variable"
  (edit_first "VariableDeclaration"
     (set_field "visibility" (JSON.STRING "public")) storage_ast)
val () = import_error_with storage_contracts "constant state variable"
  (edit_first "VariableDeclaration" (set_field "constant" (JSON.BOOL true))
     storage_ast)
val () = import_error_with storage_contracts "immutable state variable"
  (edit_first "VariableDeclaration"
     (set_field "mutability" (JSON.STRING "immutable")) storage_ast)
val () = import_error_with storage_contracts "state variable initialiser"
  (edit_first "VariableDeclaration"
     (fn JSON.OBJECT kvs =>
           JSON.OBJECT (kvs @ [("value", edit_first "Literal" I storage_ast)])
       | v => v)
     storage_ast)
val () = import_error_with (JSON.OBJECT []) "missing storage layout" storage_ast

(* The contracts output with an edit to the first layout entry, of total. *)
fun edit_layout f =
  case storage_contracts of
    JSON.OBJECT [(name, contract)] =>
      let
        val layout = JSONUtil.lookupField contract "storageLayout"
        val entries =
          case JSONUtil.lookupField layout "storage" of
            JSON.ARRAY (e :: es) => JSON.ARRAY (f e :: es)
          | _ => raise Fail "empty storage layout"
      in
        JSON.OBJECT [(name, set_field "storageLayout"
                              (set_field "storage" entries layout) contract)]
      end
  | _ => raise Fail "expected one contract"

val () = edited_unit_with (edit_layout (set_field "type" (JSON.STRING "t_uint8")))
  "layout_type_mismatch" storage_ast
val () = edited_unit_with (edit_layout (set_field "astId" (JSON.INT 999999)))
  "layout_id_mismatch" storage_ast

Theorem layout_type_mismatch_rejected:
  ¬valid_src_unit layout_type_mismatch
Proof
  CONV_TAC cv_eval
QED

Theorem layout_id_mismatch_rejected:
  ¬valid_src_unit layout_id_mismatch
Proof
  CONV_TAC cv_eval
QED
