(* Reproduce continuation growth with successive checked/calling branches.
 * TRANSLATOR_GROWTH_N selects the branch count; TRANSLATOR_GROWTH_MODE is
 * "checked" or "calling". Run after building solidityTranslatorCorpusTheory.
 *)
load "intLib";
load "solidityImportTheory";
load "solidityTranslateLib";
open HolKernel boolLib bossLib solidityCoreTheory solidityCoreWfTheory;
val _ = new_theory "translatorGrowth";

fun setting name fallback = Option.getOpt (OS.Process.getEnv name, fallback);
val branches = valOf (Int.fromString (setting "TRANSLATOR_GROWTH_N" "1"));
val mode = setting "TRANSLATOR_GROWTH_MODE" "checked";
val _ = if branches > 0 andalso (mode = "checked" orelse mode = "calling")
        then () else raise Fail "expected positive N and checked/calling mode";
fun numeral n = numSyntax.term_of_int n;
fun ident n = “AstId ^(numeral n)”;
fun atom n = “BoundAtom ^(ident n)”;
fun literal n = “ConstantAtom (IntegerValue (&^(numeral n)))”;
val u8 = “UintT 8”;
val value_type = “SingleType ^u8”;
fun decl (n, ty) = pairSyntax.mk_pair (ident n, ty);
fun decls ds = listSyntax.mk_list (map decl ds, “:ast_id # sol_type”);
fun stmts ss = listSyntax.mk_list (ss, “:core_stmt”);
fun actuals xs = listSyntax.mk_list (xs, “:core_atom”);
fun proc fid ps rs ss =
  list_mk_comb (hd (TypeBase.constructors_of “:core_procedure”),
                [ident fid, decls ps, decls rs, stmts ss]);
val callee = proc 999 [(1,u8),(2,u8)] [(3,u8)]
  [“DefineStmt (AstId 4) ^value_type
      (ScalarOperation ^u8 CheckedArithmetic AddOp [^(atom 1); ^(atom 2)])”,
   “ReturnStmt [^(atom 4)]”];
fun arm index amount =
  let
    val tmp = 10000 + index * 8 + amount;
    val args = actuals [atom 1, literal amount];
    val operation = if mode = "calling" then
        “InternalCallOperation (AstId 999) ^args”
      else “ScalarOperation ^u8 CheckedArithmetic AddOp ^args”
  in [“DefineStmt ^(ident tmp) ^value_type ^operation”,
      “CaptureBindingStmt ^(ident (tmp+3)) (AstId 1)”,
      “WriteScalarStmt ^(ident (tmp+3)) ^u8 ^(atom tmp)”]
  end;
val body = List.tabulate (branches, fn i =>
  “IfStmt ^(atom (i+2)) ^(stmts (arm i 1)) ^(stmts (arm i 2))”) @
  [“ReturnStmt [^(atom 1)]”];
val main_proc = proc 1000 ((1,u8)::List.tabulate(branches,fn i=>(i+2,“BoolT”)))
                         [(100,u8)] body;
val procs = listSyntax.mk_list ([callee,main_proc], “:core_procedure”);
val program = “<| procedures := ^procs; state_variables := []; struct_layouts := [];
                  type_declarations := []; entry_procedure := AstId 1000 |>”;
val program_def = Define ‘growth_program = ^program’;
val checked = EVAL “wf_core_program (core_program_environment ^program) ^program”;
val _ = if aconv (rhs (concl checked)) T then ()
        else (print (thm_to_string checked ^ "\n"); raise Fail "ill-formed growth fixture");
(* Source metadata supplies public function names and ids; this synthetic core
 * fixture is checked directly rather than elaborated from a source body. *)
val location = “<| loc_start := 0; loc_length := 0; loc_source := 0 |>”;
fun info n = “<| node_id := ^(numeral n); node_location := ^location |>”;
fun metadata fid name =
  “<| fn_info := ^(info fid); fn_name := ^(stringSyntax.fromMLstring name);
      fn_scope := 0; fn_visibility := "internal"; fn_mutability := "pure";
      fn_selector := NONE; fn_parameters_id := 0; fn_parameters := [];
      fn_returns_id := 0; fn_returns := []; fn_body := SrcBlock ^(info 0) [] |>”;
val functions = listSyntax.mk_list ([metadata 999 "callee", metadata 1000 "main"],
                                    “:src_function”);
val unit_def = Define ‘growth_unit =
  <| unit_info := ^(info 0); unit_path := "growth.sol";
     unit_contracts := [<| contract_info := ^(info 0); contract_name := "Growth";
       contract_scope := 0; contract_state_variables := []; contract_storage := [];
       contract_functions := ^functions |>] |>’;
fun term_nodes tm =
  if is_comb tm then 1 + term_nodes (rator tm) + term_nodes (rand tm)
  else if is_abs tm then 1 + term_nodes (snd (dest_abs tm)) else 1;
val _ = Count.counting_thms true;
val meter = Count.mk_meter ();
val started = Time.now ();
val results = solidityTranslateLib.translate_unit
  {prefix="growth_", unit_def=unit_def, program_def=program_def,
   termination=[], loops=[]};
val _ = List.app (fn {name, outcome, ...} =>
  case outcome of solidityTranslateLib.Proved _ => ()
    | solidityTranslateLib.Unsupported message => raise Fail (name ^ ": " ^ message)
    | solidityTranslateLib.Failed message => raise Fail (name ^ ": " ^ message)) results;
val elapsed = Time.- (Time.now (), started);
val counts = Count.read meter;
val definition = DB.fetch "translatorGrowth" "growth_main_def";
val generated = rhs (snd (strip_forall (concl definition)));
val _ = print ("translator-growth: mode=" ^ mode ^ " branches=" ^ Int.toString branches ^
  " nodes=" ^ Int.toString (term_nodes generated) ^
  " seconds=" ^ Time.toString elapsed ^ " prims=" ^ Int.toString (#prims counts) ^
  " axioms=" ^ Int.toString (#axioms counts) ^ "\n");
val _ = TextIO.flushOut TextIO.stdOut;
