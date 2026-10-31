structure solidityImportLib :> solidityImportLib =
struct

open HolKernel boolLib solidityImportTheory

exception ImportError of string
exception MalformedInput of string

fun fail msg = raise ImportError msg

(* JSON access, with JSONUtil errors reported against the enclosing node. *)

val field = JSONUtil.lookupField
fun string_field v k = JSONUtil.asString (field v k)
fun bool_field v k = JSONUtil.asBool (field v k)
fun int_field v k = JSONUtil.asIntInf (field v k)

(* An optional field: absent or null. *)
fun optional_field v k =
  case JSONUtil.findField v k of
    NONE => NONE
  | SOME JSON.NULL => NONE
  | SOME x => SOME x

fun node_type v = string_field v "nodeType"

fun describe v =
  (node_type v handle _ => "node") ^
  (case JSONUtil.findField v "id" handle _ => NONE of
     SOME (JSON.INT i) => " " ^ IntInf.toString i
   | _ => "")

fun within v f =
  f v
  handle ImportError msg => raise ImportError msg
       | e as JSONUtil.JSONError _ => raise MalformedInput (describe v ^ ": " ^ JSONUtil.exnMessage e)
       | e as JSONUtil.FieldNotFound _ => raise MalformedInput (describe v ^ ": " ^ JSONUtil.exnMessage e)
       | e as JSONUtil.NotObject => raise MalformedInput (describe v ^ ": " ^ JSONUtil.exnMessage e)
       | e as JSONUtil.NotArray => raise MalformedInput (describe v ^ ": " ^ JSONUtil.exnMessage e)

fun require v cond msg = if cond then () else fail (describe v ^ ": " ^ msg)

fun expect v ty = require v (node_type v = ty) ("expected " ^ ty)

(* Terms *)

fun mk_num i =
  if i < 0 then fail ("negative number " ^ IntInf.toString i)
  else numSyntax.mk_numeral (Arbnum.fromString (IntInf.toString i))

val mk_str = stringSyntax.fromMLstring

fun mk_opt ty NONE = optionSyntax.mk_none ty
  | mk_opt _ (SOME tm) = optionSyntax.mk_some tm

fun import_type name = mk_thy_type {Thy = "solidityImport", Tyop = name, Args = []}
val expr_ty = import_type "src_expr"
val stmt_ty = import_type "src_stmt"
val variable_ty = import_type "src_variable"
val function_ty = import_type "src_function"
val contract_ty = import_type "src_contract"
val struct_ty = import_type "src_struct"
val storage_entry_ty = import_type "src_storage_entry"

fun con name args =
  list_mk_comb (prim_mk_const {Thy = "solidityImport", Name = name}, args)

fun record name fields = TypeBase.mk_record (import_type name, fields)

(* "start:length:source" *)
fun location v =
  case String.fields (fn c => c = #":") (string_field v "src") of
    [s, l, f] =>
      (case (IntInf.fromString s, IntInf.fromString l, IntInf.fromString f) of
         (SOME s, SOME l, SOME f) =>
           record "src_location"
             [("loc_start", mk_num s), ("loc_length", mk_num l),
              ("loc_source", mk_num f)]
       | _ => fail (describe v ^ ": malformed src"))
  | _ => fail (describe v ^ ": malformed src")

fun info v =
  record "node_info"
    [("node_id", mk_num (int_field v "id")), ("node_location", location v)]

fun type_id v = mk_str (string_field (field v "typeDescriptions") "typeIdentifier")

(* Type names *)

fun type_name v = within v (fn v =>
  case node_type v of
    "UserDefinedTypeName" =>
      let
        val declaration = int_field v "referencedDeclaration"
        val tid = string_field (field v "typeDescriptions") "typeIdentifier"
      in
        require v (declaration >= 0 andalso String.isPrefix "t_struct$_" tid)
          "only struct user-defined types are supported";
        con "SrcStructTypeName" [info v, mk_num declaration, mk_str tid]
      end
  | "Mapping" => con "SrcMappingTypeName"
      [info v, type_name (field v "keyType"), type_name (field v "valueType")]
  | "ElementaryTypeName" =>
      let
        val name = string_field v "name"
        (* solc omits this on address keys and conversion type names. *)
        val mutability =
          case optional_field v "stateMutability" of
            SOME m => SOME (JSONUtil.asString m)
          | NONE => if name = "address" then SOME "nonpayable" else NONE
      in
        con "SrcElementaryTypeName"
          [info v, mk_str name, mk_opt stringSyntax.string_ty (Option.map mk_str mutability)]
      end
  | "ArrayTypeName" =>
      (case optional_field v "length" of
         NONE => con "SrcDynamicArrayTypeName" [info v, type_name (field v "baseType")]
       | SOME length => let
        val dimension =
          case String.fields (fn c => c = #"_")
                 (string_field (field length "typeDescriptions") "typeIdentifier") of
            ["t", "rational", n, "by", "1"] =>
              if size n > 0 andalso CharVector.all Char.isDigit n
              then IntInf.fromString n else NONE
          | _ => NONE
        val n = case dimension of
                  SOME n => if n > 0 then n else fail "nonpositive array length"
                | NONE => fail (describe v ^ ": array length is not a positive integer constant")
      in
        con "SrcArrayTypeName" [info v, type_name (field v "baseType"), mk_num n]
      end)
  | other => fail (describe v ^ ": unsupported type name " ^ other))

(* Expressions *)

fun expr v = within v (fn v =>
  case node_type v of
    "Identifier" =>
      let val declaration = int_field v "referencedDeclaration" in
        require v (declaration >= 0)
          ("built-in " ^ string_field v "name" ^ " is not supported");
        con "SrcIdentifier"
          [info v, mk_str (string_field v "name"), mk_num declaration,
           type_id v]
      end
  | "MemberAccess" =>
      (case optional_field v "referencedDeclaration" of
         SOME declaration =>
           con "SrcMemberAccess"
             [info v, expr (field v "expression"),
              mk_num (JSONUtil.asIntInf declaration), type_id v]
       | NONE =>
           (case string_field v "memberName" of
              "length" => con "SrcArrayLength"
                [info v, expr (field v "expression"), type_id v]
            | member =>
                (require v (member = "push" orelse member = "pop")
                   "unsupported built-in member";
                 con "SrcArrayMember"
                   [info v, mk_str member, expr (field v "expression"), type_id v])))
  | "Literal" =>
      (require v (not (isSome (optional_field v "subdenomination")))
         "literal subdenominations are not supported";
       con "SrcLiteral"
         [info v, mk_str (string_field v "kind"),
          mk_str (if List.exists (fn k => k = string_field v "kind")
                       ["string", "unicodeString", "hexString"] then
                    let
                      val hex = string_field v "hexValue"
                      fun digit c =
                        if c >= #"0" andalso c <= #"9" then Char.ord c - 48
                        else if c >= #"a" andalso c <= #"f" then Char.ord c - 87
                        else if c >= #"A" andalso c <= #"F" then Char.ord c - 55
                        else (fail (describe v ^ ": invalid hexValue"))
                      val () = require v (size hex mod 2 = 0) "odd hexValue length"
                    in
                      String.implode (List.tabulate (size hex div 2, fn i =>
                        Char.chr (16 * digit (String.sub (hex, 2*i)) +
                                  digit (String.sub (hex, 2*i+1)))))
                    end
                  else string_field v "value"), type_id v])
  | "UnaryOperation" =>
      con "SrcUnaryOperation"
        [info v, mk_str (string_field v "operator"),
         (if bool_field v "prefix" then T else F),
         expr (field v "subExpression"), type_id v]
  | "BinaryOperation" =>
      con "SrcBinaryOperation"
        [info v, mk_str (string_field v "operator"),
         expr (field v "leftExpression"), expr (field v "rightExpression"),
         mk_str (string_field (field v "commonType") "typeIdentifier"),
         type_id v]
  | "Assignment" =>
      con "SrcAssignment"
        [info v, mk_str (string_field v "operator"),
         expr (field v "leftHandSide"), expr (field v "rightHandSide"),
         type_id v]
  | "IndexAccess" =>
      (require v (isSome (optional_field v "indexExpression"))
         "array type expressions are not supported";
       con "SrcIndexAccess"
         [info v, expr (field v "baseExpression"),
          expr (field v "indexExpression"), type_id v])
  | "TupleExpression" =>
      (require v (not (bool_field v "isInlineArray"))
         "inline arrays are not supported";
       con "SrcTupleExpression"
         [info v,
          listSyntax.mk_list
            (JSONUtil.arrayMap
               (fn JSON.NULL => optionSyntax.mk_none expr_ty
                 | c => optionSyntax.mk_some (expr c))
               (field v "components"),
             optionSyntax.mk_option expr_ty),
          type_id v])
  | "FunctionCall" =>
      let
        val args = JSONUtil.arrayMap expr (field v "arguments")
        val callee = field v "expression"
      in
        require v (null (JSONUtil.arrayMap I (field v "names")))
          "named arguments are not supported";
        require v (not (bool_field v "tryCall")) "try calls are not supported";
        case string_field v "kind" of
          "functionCall" =>
            if node_type callee = "Identifier" andalso
               int_field callee "referencedDeclaration" < 0 then
              let
                val id = int_field callee "referencedDeclaration"
                val builtin = if id = ~18 then "RequireBuiltin"
                              else if id = ~3 then "AssertBuiltin"
                              else if id = ~19 then "RevertBuiltin"
                              else fail (describe callee ^ ": unsupported built-in declaration " ^
                                         IntInf.toString id)
                val (condition, message) =
                  case (builtin, args) of
                    ("AssertBuiltin", [c]) => (SOME c, NONE)
                  | ("RequireBuiltin", [c]) => (SOME c, NONE)
                  | ("RequireBuiltin", [c, m]) => (SOME c, SOME m)
                  | ("RevertBuiltin", []) => (NONE, NONE)
                  | ("RevertBuiltin", [m]) => (NONE, SOME m)
                  | _ => fail (describe v ^ ": unsupported built-in arguments")
              in
                con "SrcBuiltinCall" [info v, info callee, con builtin [],
                  mk_opt expr_ty condition, mk_opt expr_ty message, type_id v]
              end
            else con "SrcFunctionCall"
              [info v, expr callee, listSyntax.mk_list (args, expr_ty), type_id v]
        | "typeConversion" =>
            (require v (length args = 1) "a conversion takes one argument";
             within callee (fn c => expect c "ElementaryTypeNameExpression");
             con "SrcTypeConversion"
               [info v, type_name (field callee "typeName"), hd args,
                type_id v])
        | kind => fail (describe v ^ ": unsupported call kind " ^ kind)
      end
  | other => fail (describe v ^ ": unsupported expression " ^ other))

fun optional_expr v k =
  mk_opt expr_ty (Option.map expr (optional_field v k))

(* Declarations *)

(* A local, parameter or return variable, or, given state, a state variable. *)
fun declaration state v = within v (fn v =>
  (expect v "VariableDeclaration";
   require v (not (bool_field v "constant")) "constants are not supported";
   require v (bool_field v "stateVariable" = state)
     (if state then "expected a state variable"
      else "expected a local variable");
   require v (string_field v "mutability" = "mutable")
     "immutable variables are not supported";
   require v (not (isSome (optional_field v "value")))
     "declaration values are not supported";
   require v (not state orelse string_field v "visibility" <> "public")
     "public state variables are not supported";
   record "src_variable"
     [("var_info", info v), ("var_name", mk_str (string_field v "name")),
      ("var_scope", mk_num (int_field v "scope")),
      ("var_type_name", type_name (field v "typeName")),
      ("var_type_id", type_id v),
      ("var_location", mk_str (string_field v "storageLocation"))]))

val variable = declaration false

(* Statements *)

fun stmt v = within v (fn v =>
  case node_type v of
    "Block" => con "SrcBlock" [info v, stmts (field v "statements")]
  | "UncheckedBlock" =>
      con "SrcUncheckedBlock" [info v, stmts (field v "statements")]
  | "ExpressionStatement" =>
      con "SrcExpressionStatement" [info v, expr (field v "expression")]
  | "VariableDeclarationStatement" =>
      con "SrcVariableDeclarationStatement"
        [info v,
         listSyntax.mk_list
           (JSONUtil.arrayMap
              (fn JSON.NULL => optionSyntax.mk_none numSyntax.num
                | i => optionSyntax.mk_some (mk_num (JSONUtil.asIntInf i)))
              (field v "assignments"),
            optionSyntax.mk_option numSyntax.num),
         listSyntax.mk_list
           (JSONUtil.arrayMap
              (fn JSON.NULL => optionSyntax.mk_none variable_ty
                | d => optionSyntax.mk_some (variable d))
              (field v "declarations"),
            optionSyntax.mk_option variable_ty),
         optional_expr v "initialValue"]
  | "IfStatement" =>
      con "SrcIfStatement"
        [info v, expr (field v "condition"), stmt (field v "trueBody"),
         optional_stmt v "falseBody"]
  | "WhileStatement" =>
      con "SrcWhileStatement"
        [info v, expr (field v "condition"), stmt (field v "body")]
  | "DoWhileStatement" =>
      con "SrcDoWhileStatement"
        [info v, stmt (field v "body"), expr (field v "condition")]
  | "ForStatement" =>
      con "SrcForStatement"
        [info v, optional_stmt v "initializationExpression",
         optional_expr v "condition", optional_stmt v "loopExpression",
         stmt (field v "body")]
  | "Break" => con "SrcBreak" [info v]
  | "Continue" => con "SrcContinue" [info v]
  | "Return" =>
      con "SrcReturn"
        [info v, mk_num (int_field v "functionReturnParameters"),
         optional_expr v "expression"]
  | other => fail (describe v ^ ": unsupported statement " ^ other))
and stmts v = listSyntax.mk_list (JSONUtil.arrayMap stmt v, stmt_ty)
and optional_stmt v k = mk_opt stmt_ty (Option.map stmt (optional_field v k))

(* Functions, contracts and source units *)

fun parameter_list v = within v (fn v =>
  (expect v "ParameterList";
   (mk_num (int_field v "id"),
    listSyntax.mk_list
      (JSONUtil.arrayMap variable (field v "parameters"), variable_ty))))

fun function v = within v (fn v =>
  let
    val (params_id, params) = parameter_list (field v "parameters")
    val (returns_id, returns) = parameter_list (field v "returnParameters")
  in
    expect v "FunctionDefinition";
    require v (string_field v "kind" = "function")
      ("unsupported function kind " ^ string_field v "kind");
    require v (bool_field v "implemented") "unimplemented functions";
    require v (null (JSONUtil.arrayMap I (field v "modifiers")))
      "modifiers are not supported";
    require v (not (bool_field v "virtual")) "virtual functions";
    require v (not (isSome (optional_field v "overrides")))
      "overrides are not supported";
    record "src_function"
      [("fn_info", info v), ("fn_name", mk_str (string_field v "name")),
       ("fn_scope", mk_num (int_field v "scope")),
       ("fn_visibility", mk_str (string_field v "visibility")),
       ("fn_mutability", mk_str (string_field v "stateMutability")),
       ("fn_selector",
        mk_opt stringSyntax.string_ty
          (Option.map (mk_str o JSONUtil.asString)
             (optional_field v "functionSelector"))),
       ("fn_parameters_id", params_id), ("fn_parameters", params),
       ("fn_returns_id", returns_id), ("fn_returns", returns),
       ("fn_body", stmt (field v "body"))]
  end)

(* An entry of a contract's storageLayout. *)
fun storage_entry v = within v (fn v =>
  record "src_storage_entry"
    [("storage_id", mk_num (int_field v "astId")),
     ("storage_slot",
      case IntInf.fromString (string_field v "slot") of
        SOME i => mk_num i
      | NONE => fail "malformed storage slot"),
     ("storage_offset", mk_num (int_field v "offset")),
     ("storage_type_id", mk_str (string_field v "type"))])

fun struct_declaration types v = within v (fn v =>
  let
    val () = expect v "StructDefinition"
    val key = "t_struct(" ^ string_field v "name" ^ ")" ^
              IntInf.toString (int_field v "id") ^ "_storage"
    val layout =
      case (case types of JSON.NULL => NONE | _ => JSONUtil.findField types key) of
        NONE => NONE
      | SOME desc =>
          (require v (string_field desc "encoding" = "inplace")
             "struct layout encoding must be inplace";
           SOME (pairSyntax.mk_pair
             (case IntInf.fromString (string_field desc "numberOfBytes") of
                SOME bytes => mk_num bytes
              | NONE => fail "malformed struct layout size",
              listSyntax.mk_list
                (JSONUtil.arrayMap storage_entry (field desc "members"),
                 storage_entry_ty))))
  in
    record "src_struct"
      [("struct_info", info v),
       ("struct_scope", mk_num (int_field v "scope")),
       ("struct_members", listSyntax.mk_list
         (JSONUtil.arrayMap (declaration false) (field v "members"), variable_ty)),
       ("struct_layout", mk_opt
         (pairSyntax.mk_prod (numSyntax.num, listSyntax.mk_list_type storage_entry_ty))
         layout)]
  end)

(* The selected contract's layout also describes file-level struct types
 * referenced by its state variables.
 *)
fun contract external_structs contracts v = within v (fn v =>
  let
    val id = int_field v "id"
    val name = string_field v "name"
    val members = JSONUtil.arrayMap I (field v "nodes")
    fun members_of ty = List.filter (fn m => node_type m = ty) members
    val () =
      List.app (fn m => within m (fn m =>
                  require m (node_type m = "FunctionDefinition" orelse
                             node_type m = "VariableDeclaration" orelse
                             node_type m = "StructDefinition")
                    "unsupported contract member"))
        members
    val layout =
      JSONUtil.get (contracts,
        [JSONUtil.SEL name, JSONUtil.SEL "storageLayout"])
  in
    expect v "ContractDefinition";
    require v (string_field v "contractKind" = "contract")
      ("unsupported contract kind " ^ string_field v "contractKind");
    require v (not (bool_field v "abstract")) "abstract contracts";
    require v (null (JSONUtil.arrayMap I (field v "baseContracts")))
      "inheritance is not supported";
    require v (JSONUtil.arrayMap JSONUtil.asIntInf
                 (field v "linearizedBaseContracts") = [id])
      "inheritance is not supported";
    record "src_contract"
      [("contract_info", info v),
       ("contract_name", mk_str (string_field v "name")),
       ("contract_scope", mk_num (int_field v "scope")),
       ("contract_state_variables",
        listSyntax.mk_list
          (map (declaration true) (members_of "VariableDeclaration"),
           variable_ty)),
       ("contract_storage",
        listSyntax.mk_list
          (JSONUtil.arrayMap storage_entry (field layout "storage"), storage_entry_ty)),
       ("contract_structs", listSyntax.mk_list
          (map (struct_declaration (field layout "types"))
             (external_structs @ members_of "StructDefinition"), struct_ty)),
       ("contract_functions",
        listSyntax.mk_list
          (map function (members_of "FunctionDefinition"), function_ty))]
  end)

(* File-level structs accompany each contract that can refer to them;
 * pragmas carry no semantics for the pinned profile.
 *)
fun import_source_unit v contracts = within v (fn v =>
  let
    val members = JSONUtil.arrayMap I (field v "nodes")
    val structs = List.filter (fn m => node_type m = "StructDefinition") members
    fun member m acc =
      case node_type m of
        "PragmaDirective" => acc
      | "StructDefinition" => acc
      | "ContractDefinition" => contract structs contracts m :: acc
      | other => fail (describe m ^ ": unsupported source unit member " ^ other)
    val contracts =
      List.foldr (fn (m, acc) => within m (fn m => member m acc)) []
        members
  in
    expect v "SourceUnit";
    record "src_unit"
      [("unit_info", info v),
       ("unit_path", mk_str (string_field v "absolutePath")),
       ("unit_contracts", listSyntax.mk_list (contracts, contract_ty))]
  end)

fun read_artifact path =
  let
    val artifact = JSONParser.parseFile path
      handle e => fail (path ^ ": " ^ General.exnMessage e)
    val format = string_field artifact "format"
      handle e => fail (path ^ ": " ^ JSONUtil.exnMessage e)
  in
    if format <> "solidity-hol-solc-artifact-v1" then
      fail (path ^ ": unsupported artifact format " ^ format)
    else artifact
  end

fun artifact_deployed_bytecode path source contract =
  JSONUtil.asString
    (JSONUtil.get (read_artifact path,
       [JSONUtil.SEL "output", JSONUtil.SEL "contracts", JSONUtil.SEL source,
        JSONUtil.SEL contract, JSONUtil.SEL "evm",
        JSONUtil.SEL "deployedBytecode", JSONUtil.SEL "object"]))
  handle ImportError msg => raise ImportError msg
       | e => fail (path ^ ": no deployed bytecode for " ^ contract ^ ": " ^
                    JSONUtil.exnMessage e)

fun import_artifact path source =
  let
    val artifact = read_artifact path
    fun get keys what =
      JSONUtil.get (artifact, map JSONUtil.SEL keys)
      handle e => fail (path ^ ": no " ^ what ^ " for " ^ source ^ ": " ^
                        JSONUtil.exnMessage e)
  in
    import_source_unit (get ["output", "sources", source, "ast"] "AST")
      (get ["output", "contracts", source] "contracts")
  end

end
