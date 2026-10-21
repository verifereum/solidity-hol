structure solidityImportLib :> solidityImportLib =
struct

open HolKernel boolLib solidityImportTheory

exception ImportError of string

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
       | e as JSONUtil.JSONError _ => fail (describe v ^ ": " ^ JSONUtil.exnMessage e)
       | e as JSONUtil.FieldNotFound _ => fail (describe v ^ ": " ^ JSONUtil.exnMessage e)
       | e as JSONUtil.NotObject => fail (describe v ^ ": " ^ JSONUtil.exnMessage e)
       | e as JSONUtil.NotArray => fail (describe v ^ ": " ^ JSONUtil.exnMessage e)

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
  (expect v "ElementaryTypeName";
   con "SrcElementaryTypeName"
     [info v, mk_str (string_field v "name"),
      mk_opt stringSyntax.string_ty
        (Option.map (mk_str o JSONUtil.asString)
           (optional_field v "stateMutability"))]))

(* Expressions *)

fun expr v = within v (fn v =>
  case node_type v of
    "Identifier" =>
      con "SrcIdentifier"
        [info v, mk_str (string_field v "name"),
         mk_num (int_field v "referencedDeclaration"), type_id v]
  | "Literal" =>
      (require v (not (isSome (optional_field v "subdenomination")))
         "literal subdenominations are not supported";
       con "SrcLiteral"
         [info v, mk_str (string_field v "kind"),
          mk_str (string_field v "value"), type_id v])
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
            con "SrcFunctionCall"
              [info v, expr callee, listSyntax.mk_list (args, expr_ty),
               type_id v]
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

fun variable v = within v (fn v =>
  (expect v "VariableDeclaration";
   require v (not (bool_field v "constant")) "constants are not supported";
   require v (not (bool_field v "stateVariable"))
     "state variables are not supported";
   require v (string_field v "mutability" = "mutable")
     "immutable variables are not supported";
   require v (not (isSome (optional_field v "value")))
     "declaration values are not supported";
   record "src_variable"
     [("var_info", info v), ("var_name", mk_str (string_field v "name")),
      ("var_scope", mk_num (int_field v "scope")),
      ("var_type_name", type_name (field v "typeName")),
      ("var_type_id", type_id v),
      ("var_location", mk_str (string_field v "storageLocation"))]))

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

fun contract v = within v (fn v =>
  let val id = int_field v "id" in
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
       ("contract_functions",
        listSyntax.mk_list
          (JSONUtil.arrayMap function (field v "nodes"), function_ty))]
  end)

(* Pragmas carry no semantics for the pinned profile; any other source-unit
 * member is rejected.
 *)
fun import_source_unit v = within v (fn v =>
  let
    fun member m acc =
      case node_type m of
        "PragmaDirective" => acc
      | "ContractDefinition" => contract m :: acc
      | other => fail (describe m ^ ": unsupported source unit member " ^ other)
    val contracts =
      List.foldr (fn (m, acc) => within m (fn m => member m acc)) []
        (JSONUtil.arrayMap I (field v "nodes"))
  in
    expect v "SourceUnit";
    record "src_unit"
      [("unit_info", info v),
       ("unit_path", mk_str (string_field v "absolutePath")),
       ("unit_contracts", listSyntax.mk_list (contracts, contract_ty))]
  end)

fun import_artifact path source =
  let
    val artifact = JSONParser.parseFile path
      handle e => fail (path ^ ": " ^ General.exnMessage e)
    val format = string_field artifact "format"
      handle e => fail (path ^ ": " ^ JSONUtil.exnMessage e)
  in
    if format <> "solidity-hol-solc-artifact-v1" then
      fail (path ^ ": unsupported artifact format " ^ format)
    else
      import_source_unit
        (JSONUtil.get (artifact,
           [JSONUtil.SEL "output", JSONUtil.SEL "sources", JSONUtil.SEL source,
            JSONUtil.SEL "ast"])
         handle e => fail (path ^ ": no AST for " ^ source ^ ": " ^
                           JSONUtil.exnMessage e))
  end

end
