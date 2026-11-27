(* testdata/frontend/pure_core.sol through import, elaboration, the core
 * checker and the evaluator. Expected results are worked out from the
 * language definition; solidityDifferentialTest compares them against the
 * compiled bytecode.
 *)
Theory solidityElaborateTest
Ancestors
  solidityElaborate solidityImportTest
Libs
  cv_transLib intLib wordsLib solidityImportLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [
  "../testdata/differential/expected/constant_conversions.json",
  "../testdata/differential/expected/pointer_only_structs.json"
]

val elaborated = cv_eval “elaborate_unit pure_core”;

Definition pure_core_program_def:
  pure_core_program = ^(elaborated |> concl |> rhs |> optionSyntax.dest_some)
End

val () = cv_auto_trans pure_core_program_def;

Theorem pure_core_elaborates:
  elaborate_unit pure_core = SOME pure_core_program
Proof
  simp[elaborated, pure_core_program_def]
QED

Theorem pure_core_program_wf:
  wf_core_program (core_program_environment pure_core_program)
    pure_core_program
Proof
  EVAL_TAC
QED

Definition constant_conversions_def:
  constant_conversions = ^(import_artifact
    "../testdata/differential/expected/constant_conversions.json"
    "testdata/differential/constant_conversions.sol")
End

val () = cv_auto_trans constant_conversions_def;
val conversions_elaborated = cv_eval “elaborate_unit constant_conversions”;

Definition constant_conversions_program_def:
  constant_conversions_program =
    ^(conversions_elaborated |> concl |> rhs |> optionSyntax.dest_some)
End

val () = cv_auto_trans constant_conversions_program_def;

Theorem constant_conversions_elaborate:
  elaborate_unit constant_conversions = SOME constant_conversions_program
Proof
  simp[conversions_elaborated, constant_conversions_program_def]
QED

(* Partial admission must not hide a rejected conversion from the core check. *)
Theorem constant_conversions_all_admitted:
  MAP (λf. f.fn_name) (HD constant_conversions.unit_contracts).contract_functions =
    ["addressToUint"; "addressToBytes"; "assignmentToInt";
     "assignmentToBytes"; "lengthToBytes"; "lengthToUint8"] ∧
  EVERY (λf. MEM (AstId f.fn_info.node_id)
                (MAP (λp. p.procedure_id) constant_conversions_program.procedures))
    (HD constant_conversions.unit_contracts).contract_functions ∧
  constant_conversions_program.unsupported_procedures = []
Proof
  EVAL_TAC
QED

Theorem constant_conversions_program_wf:
  wf_core_program (core_program_environment constant_conversions_program)
    constant_conversions_program
Proof
  CONV_TAC cv_eval
QED

Overload iv = “λi. ScalarValue (IntegerValue i)”
Overload bv = “λb. ScalarValue (BoolValue b)”

Definition initial_state_def:
  initial_state = <|
    world := <| accounts := empty_accounts;
                transient := empty_transient_storage;
                logs := []; original := empty_accounts; to_delete := [] |>;
    frame := <| self_address := 0w; code_address := 0w; sender_address := 0w;
                call_value := 0; call_data := []; static_context := F;
                tx_params := <| origin := 0w; gasPrice := 0; baseFeePerGas := 0;
                  baseFeePerBlobGas := 0; blockNumber := 0; blockTimeStamp := 0;
                  blockCoinBase := 0w; blockGasLimit := 0; prevRandao := 0w;
                  prevHashes := []; blobHashes := []; chainId := 0;
                  authRefund := 0 |> |>;
    scopes := [];
    (* the free memory pointer at 0x40 holds 0x80, as the prologue leaves it *)
    memory := FEMPTY |+ (0x5F, 0x80w); memory_size := 96;
    immutables := SOME FEMPTY;
    targets := FEMPTY; return_data := SOME []
  |>
End

(* The procedure of a function of the fixture, by name. *)
Definition function_id_def:
  function_id name =
    case pure_core.unit_contracts of
      c :: _ =>
        (case FILTER (λf. f.fn_name = name) c.contract_functions of
           f :: _ => AstId f.fn_info.node_id
         | [] => AstId 0)
    | [] => AstId 0
End

Definition run_function_def:
  run_function fuel name args =
    (invoke_source fuel (core_program_environment pure_core_program)
       (function_id name) (MAP iv args) initial_state []).completion
End

val () = cv_auto_trans run_function_def;

Theorem add_returns:
  run_function 50 "add" [2; 3] = ReturnCompletion [iv 5]
Proof
  CONV_TAC cv_eval
QED

Theorem add_overflow_panics:
  run_function 50 "add" [200; 100] = PanicCompletion 0x11
Proof
  CONV_TAC cv_eval
QED

Theorem unchecked_add_wraps:
  run_function 50 "wrappingAdd" [200; 100] = ReturnCompletion [iv 44]
Proof
  CONV_TAC cv_eval
QED

Theorem while_prelude_continue_exit:
  run_function 50 "count" [5] = ReturnCompletion [iv 2; iv 5]
Proof
  CONV_TAC cv_eval
QED

Theorem while_break:
  run_function 50 "count" [100] = ReturnCompletion [iv 3; iv 6]
Proof
  CONV_TAC cv_eval
QED

(* The for loop skips 2 by continue, which still runs i++. *)
Theorem for_continue_increments:
  run_function 50 "sum" [5] = ReturnCompletion [iv 8]
Proof
  CONV_TAC cv_eval
QED

Theorem do_while_runs_once:
  run_function 50 "doubleUntil" [0] = ReturnCompletion [iv 2]
Proof
  CONV_TAC cv_eval
QED

Theorem do_while_loops:
  run_function 50 "doubleUntil" [7] = ReturnCompletion [iv 8]
Proof
  CONV_TAC cv_eval
QED

Theorem recursion:
  run_function 50 "fact" [5] = ReturnCompletion [iv 120]
Proof
  CONV_TAC cv_eval
QED

Theorem multiple_returns:
  run_function 50 "divmod" [17; 5] = ReturnCompletion [iv 3; iv 2]
Proof
  CONV_TAC cv_eval
QED

Theorem division_by_zero_panics:
  run_function 50 "divmod" [1; 0] = PanicCompletion 0x12
Proof
  CONV_TAC cv_eval
QED

Theorem tuple_assignment:
  run_function 50 "swap" [] = ReturnCompletion [iv 2; iv 3]
Proof
  CONV_TAC cv_eval
QED

Theorem locals_and_tuple_declarations:
  run_function 50 "locals" [10] = ReturnCompletion [iv 10]
Proof
  CONV_TAC cv_eval
QED

Theorem narrowing_conversion:
  run_function 50 "narrow" [300] = ReturnCompletion [iv 44; bv F]
Proof
  CONV_TAC cv_eval
QED

Theorem negate_overflow_panics:
  run_function 50 "negate" [-128] = PanicCompletion 0x11
Proof
  CONV_TAC cv_eval
QED

Theorem negate_returns:
  run_function 50 "negate" [5] = ReturnCompletion [iv (-5)]
Proof
  CONV_TAC cv_eval
QED

Theorem and_skips_division:
  run_function 50 "guardedDivide" [0] = ReturnCompletion [bv F]
Proof
  CONV_TAC cv_eval
QED

Theorem and_evaluates_division:
  run_function 50 "guardedDivide" [5] = ReturnCompletion [bv T]
Proof
  CONV_TAC cv_eval
QED

Theorem and_division_panics:
  run_function 50 "badDivide" [0] = PanicCompletion 0x12
Proof
  CONV_TAC cv_eval
QED

Theorem or_skips_increment:
  run_function 50 "shortCircuit" [10] = ReturnCompletion [bv T; iv 0]
Proof
  CONV_TAC cv_eval
QED

Theorem or_runs_increment:
  run_function 50 "shortCircuit" [1] = ReturnCompletion [bv T; iv 1]
Proof
  CONV_TAC cv_eval
QED

Theorem left_operand_panics_first:
  run_function 50 "panicOrder" [0] = PanicCompletion 0x11
Proof
  CONV_TAC cv_eval
QED

Theorem left_argument_panics_first:
  run_function 50 "argumentOrder" [0] = PanicCompletion 0x11
Proof
  CONV_TAC cv_eval
QED

Theorem compound_assignment_reads_after_rhs:
  run_function 50 "compoundOrder" [1] = ReturnCompletion [iv 10]
Proof
  CONV_TAC cv_eval
QED

Definition missing_struct_layout_unit_def:
  missing_struct_layout_unit =
    case struct_unit.unit_contracts of
      c :: cs =>
        struct_unit with unit_contracts :=
          (c with contract_structs :=
            MAP (λs. s with struct_layout := NONE) c.contract_structs) :: cs
    | [] => struct_unit
End
val () = cv_auto_trans missing_struct_layout_unit_def;

Theorem missing_struct_layouts_computed_for_execution:
  IS_SOME (elaborate_unit struct_unit) ∧
  valid_src_unit missing_struct_layout_unit ∧
  case elaborate_unit missing_struct_layout_unit of
    SOME p => wf_core_program (core_program_environment p) p
  | NONE => F
Proof
  rpt conj_tac >- CONV_TAC cv_eval >- CONV_TAC cv_eval >>
  CONV_TAC cv_eval
QED

Theorem computed_struct_layouts_match_solc:
  elaborate_unit missing_struct_layout_unit = elaborate_unit struct_unit ∧
  elab_struct_layouts (REVERSE (HD missing_struct_layout_unit.unit_contracts).contract_structs) =
    OPTION_MAP REVERSE (elab_struct_layouts (HD struct_unit.unit_contracts).contract_structs)
Proof
  conj_tac >- CONV_TAC cv_eval >>
  (* CV needs the fixture to have a head contract. *)
  ‘missing_struct_layout_unit.unit_contracts ≠ []’ by
    (REWRITE_TAC [GSYM listTheory.NULL_EQ] >> CONV_TAC cv_eval) >>
  pop_assum (fn nonempty =>
    CONV_TAC (LAND_CONV (fn tm => MP (cv_eval tm) nonempty))) >>
  EVAL_TAC >>
  simp[solidityCoreTheory.core_struct_layout_component_equality,
       solidityCoreTheory.core_state_variable_component_equality]
QED

Definition unlayoutable_structs_def:
  unlayoutable_structs =
    case struct_unit.unit_contracts of
      c :: _ =>
        (case c.contract_structs of
           s :: _ => [s with <| struct_layout := NONE;
             struct_members := MAP (λv. v with var_location := SOME MemoryLoc)
               s.struct_members |>]
         | [] => [])
    | [] => []
End
val () = cv_auto_trans unlayoutable_structs_def;

Theorem unlayoutable_struct_still_omitted:
  LENGTH unlayoutable_structs = 1 ∧
  elab_struct_layouts unlayoutable_structs = SOME []
Proof
  CONV_TAC cv_eval
QED

Definition pointer_only_structs_unit_def:
  pointer_only_structs_unit = ^(import_artifact
    "../testdata/differential/expected/pointer_only_structs.json"
    "testdata/differential/pointer_only_structs.sol")
End
val () = cv_auto_trans pointer_only_structs_unit_def;

Definition pointer_only_layouts_def:
  pointer_only_layouts =
    case pointer_only_structs_unit.unit_contracts of
      c :: _ => computed_struct_layouts (LENGTH c.contract_structs) c.contract_structs
    | [] => []
End
val () = cv_auto_trans pointer_only_layouts_def;

Definition pointer_only_layout_summary_def:
  pointer_only_layout_summary =
    (EVERY (λs. s.struct_layout = NONE)
       (FLAT (MAP (λc. c.contract_structs) pointer_only_structs_unit.unit_contracts)),
     MAP (λs. (s.struct_slots,
       MAP (λv. (w2n v.state_slot, v.state_offset)) s.struct_fields)) pointer_only_layouts)
End
val () = cv_auto_trans pointer_only_layout_summary_def;

(* The outer struct's fixed uint24[11] uses two slots, not one; its nested
 * struct is declared later. Neither has a compiler-provided layout. *)
Theorem pointer_only_packing:
  LENGTH pointer_only_layouts = 3 ∧
  FST pointer_only_layout_summary ∧
  MEM (11, [(0, 0); (0, 16); (1, 0); (2, 0); (4, 0); (5, 0);
            (7, 0); (8, 0); (9, 0); (10, 0)])
    (SND pointer_only_layout_summary)
Proof
  CONV_TAC cv_eval
QED

val info0 = “<| node_id := 0;
                node_location := <| loc_start := 0; loc_length := 0;
                                    loc_source := 0 |> |>”;
fun at id = “^info0 with node_id := ^(numSyntax.term_of_int id)”;
val ctx0 = “<| functions := []; static_functions := [];
               supers := []; structs := []; enums := [];
               events := []; variables := []; state := []; locations := [];
               immutables := []; constants := []; returns := [];
               placeholder := NONE; mode := CheckedArithmetic;
               scope := 0; returns_id := 0; in_loop := F; bad_ids := [] |>”;

Theorem no_exponent_assignment:
  compound_operator (SOME SrcExp) = NONE ∧
  compound_operator (SOME SrcAdd) = SOME AddOp
Proof
  EVAL_TAC
QED

val local_declaration =
  “SrcVariableDeclarationStatement ^info0 [SOME 1]
     [SOME <| var_info := ^(at 1); var_name := "x"; var_scope := 0;
              var_type_name := SrcElementaryTypeName ^info0 "uint256" NONE;
              var_type_id := "t_uint256"; var_transient := F; var_location := NONE |>]
     NONE”;
val true_condition = “SrcLiteral ^info0 BoolLiteral "true" "t_bool"”;

(* Statements the compiler does not produce: a declaration as the body of an
 * if or a loop (it must be a statement of a block), and a fractional literal
 * in a tuple, even at a hole. *)
Theorem declaration_body_and_tuple_fraction_rejected:
  ISL (elab_stmt ^ctx0 2 ^local_declaration) ∧
  elab_stmt ^ctx0 2 (SrcIfStatement ^info0 ^true_condition ^local_declaration NONE) =
    INR [(0, "declaration as a body")] ∧
  elab_stmt ^ctx0 2 (SrcWhileStatement ^info0 ^true_condition ^local_declaration) =
    INR [(0, "declaration as a body")] ∧
  elab_stmt ^ctx0 2 (SrcVariableDeclarationStatement ^info0 [NONE] [NONE]
    (SOME (SrcLiteral ^info0 NumberLiteral "" "t_rational_1_by_2"))) =
    INR [(0, "rational number value")]
Proof
  EVAL_TAC
QED

val bytes_context =
  “^ctx0 with variables := [(1, LocatedT MemoryLoc BytesT); (2, FixedBytesT 32)]”;
fun to_bytes16 e =
  “SrcTypeConversion ^info0 (SrcElementaryTypeName ^info0 "bytes16" NONE) ^e "t_bytes16"”;

(* Dynamic bytes and fixed bytes both convert to a fixed-size prefix. *)
Theorem bytes_to_fixed_bytes_admitted:
  ISL (elab_expr ^bytes_context 3
    ^(to_bytes16 “SrcIdentifier ^info0 "b" 1 "t_bytes_memory_ptr"”)) ∧
  ISL (elab_expr ^bytes_context 3
    ^(to_bytes16 “SrcIdentifier ^info0 "w" 2 "t_bytes32"”))
Proof
  EVAL_TAC
QED

(* Rejection reasons: a list of statements reports every statement that
 * fails, and a statement after a failed declaration only its own blockers.
 * The declared variable is bound if its type is supported, and otherwise
 * a reference to it adds no blocker, the declaration having reported it. *)
fun local_y tn = “<| var_info := ^(at 4); var_name := "y"; var_scope := 0;
                     var_type_name := ^tn; var_type_id := "t_uint256";
                     var_transient := F; var_location := NONE |>”;
val supported_y = local_y “SrcElementaryTypeName ^(at 7) "uint256" NONE”;
val unsupported_y = local_y “SrcUnsupportedTypeName ^(at 7) "function type"”;
val read_y = “SrcExpressionStatement ^(at 5) (SrcIdentifier ^(at 6) "y" 4 "t_uint256")”;

(* A storage or calldata reference local declared without a value starts as
 * a placeholder reference, which solc rejects reading before an assignment;
 * a storage location holding no object has no default. *)
Theorem reference_locals_default_to_placeholders:
  default_operation (LocatedT StorageLoc (ArrayT (UintT 256) NONE)) =
    SOME (DefaultReferenceOperation StorageLoc (ArrayT (UintT 256) NONE)) ∧
  default_operation (LocatedT StorageLoc (MappingT (UintT 256) (UintT 256))) =
    SOME (DefaultReferenceOperation StorageLoc (MappingT (UintT 256) (UintT 256))) ∧
  default_operation (LocatedT StorageLoc (StructT (AstId 7))) =
    SOME (DefaultReferenceOperation StorageLoc (StructT (AstId 7))) ∧
  default_operation (LocatedT CalldataLoc BytesT) =
    SOME (DefaultReferenceOperation CalldataLoc BytesT) ∧
  default_operation (LocatedT StorageLoc (UintT 256)) = NONE
Proof
  EVAL_TAC
QED

Theorem storage_pointer_declared_without_value:
  let p = <| var_info := ^(at 4); var_name := "p"; var_scope := 0;
             var_type_name := SrcElementaryTypeName ^(at 7) "bytes" NONE;
             var_type_id := "t_bytes_storage_ptr"; var_transient := F;
             var_location := SOME StorageLoc |> in
    elab_stmt ^ctx0 10
      (SrcVariableDeclarationStatement ^(at 3) [SOME 4] [SOME p] NONE) =
    INL (([DefineStmt (AstId 4) (SingleType (LocatedT StorageLoc BytesT))
             (DefaultReferenceOperation StorageLoc BytesT)],
          ^ctx0 with variables := [(4, LocatedT StorageLoc BytesT)]), 10)
Proof
  EVAL_TAC
QED

Theorem independent_failures_all_report:
  elab_stmts ^ctx0 10 [SrcBreak ^(at 1); SrcContinue ^(at 2)] =
  INR [(1, "break outside a loop"); (2, "continue outside a loop")]
Proof
  EVAL_TAC
QED

Theorem failed_declaration_reference_adds_no_blocker:
  elab_stmts ^ctx0 10
    [SrcVariableDeclarationStatement ^(at 3) [SOME 4] [SOME ^unsupported_y]
       (SOME (SrcLiteral ^(at 8) NumberLiteral "1" "t_rational_1_by_1"));
     ^read_y] =
  INR [(7, "function type")] ∧
  elab_stmts ^ctx0 10
    [SrcVariableDeclarationStatement ^(at 3) [SOME 4] [SOME ^supported_y]
       (SOME (SrcLiteral ^(at 8) NumberLiteral "" "t_rational_1_by_2"));
     ^read_y] =
  INR [(8, "rational number value")]
Proof
  EVAL_TAC
QED

(* A function whose parameter or return variable fails still reports its
 * body's blockers; a reference to the failed parameter, or a return of a
 * value for the failed return variable, adds none. *)
val empty_contract =
  “<| contract_info := ^info0; contract_name := "C"; contract_scope := 0;
      contract_bases := []; contract_state_variables := [];
      contract_immutables := []; contract_initializers := [];
      contract_libraries := []; contract_constants := [];
      contract_base_arguments := []; contract_static_calls := []; contract_storage := [];
      contract_structs := []; contract_enums := []; contract_events := [];
      contract_modifiers := []; contract_functions := [];
      contract_library_functions := []; contract_getters := [];
      contract_function_ids := [] |>”;
fun function_of ps rs ss =
  “<| fn_info := ^(at 1); fn_name := "f"; fn_scope := 0;
      fn_kind := FunctionKind; fn_visibility := InternalVisibility;
      fn_mutability := NonpayableMut; fn_selector := NONE;
      fn_base_functions := []; fn_parameters_id := 2; fn_parameters := ^ps;
      fn_nominal_parameters := [];
      fn_returns_id := 3; fn_returns := ^rs; fn_modifiers := [];
      fn_super_calls := []; fn_static_calls := []; fn_body := SrcBlock ^(at 9) ^ss;
      fn_unsupported := NONE |>”;
val break_11 = “SrcBreak ^(at 11)”;
val return_1 = “SrcReturn ^(at 12) 3
                  (SOME (SrcLiteral ^(at 13) NumberLiteral "1" "t_rational_1_by_1"))”;

val failed_parameter = function_of “[^unsupported_y]” “[] : src_variable list” “[^read_y; ^break_11]”;
val failed_return = function_of “[] : src_variable list” “[^unsupported_y]” “[^return_1; ^break_11]”;

Theorem failed_variables_keep_body_blockers:
  elab_function ^ctx0 ^empty_contract T F 10 ^failed_parameter =
  INR [(7, "function type"); (11, "break outside a loop")] ∧
  elab_function ^ctx0 ^empty_contract T F 10 ^failed_return =
  INR [(7, "function type"); (11, "break outside a loop")]
Proof
  EVAL_TAC
QED

(* A try statement of a call that elaborates but is not an external call
 * still reports both clauses' blockers. *)
Theorem unsupported_try_keeps_clause_blockers:
  elab_stmt ^ctx0 10
    (SrcTryStatement ^(at 19) (SrcLiteral ^(at 20) BoolLiteral "true" "t_bool")
       ^(at 21) [] (SrcBreak ^(at 11))
       [SrcCatchClause ^(at 22) GenericCatch [] (SrcContinue ^(at 12))]) =
  INR [(19, "unsupported try statement"); (11, "break outside a loop");
       (12, "continue outside a loop")]
Proof
  EVAL_TAC
QED

val success_n = “^supported_y with <| var_scope := 21; var_name := "n" |>”;
val success_b = “^success_n with
  <| var_info := ^(at 5); var_name := "";
     var_type_name := SrcElementaryTypeName ^(at 8) "bool" NONE;
     var_type_id := "t_bool" |>”;
val success_call = “SrcExternalCall ^(at 30)
  <| ext_selector := [0w; 0w; 0w; 0w]; ext_mutability := NonpayableMut; ext_kind := ExternalCall; ext_bound := F;
     ext_signature := FunctionSignature [] [^success_n; ^success_b] |>
  [] [SrcIdentifier ^(at 31) "target" 40 "t_address"] []
  "t_tuple$_t_uint256_$_t_bool_$"”;
val success_body = “SrcBlock ^(at 22) []”;

Theorem try_success_requires_all_types_and_scope:
  try_call [] 11 ^success_call 21 [^success_n] ^success_body []
    (BoundAtom (AstId 10)) = NONE ∧
  try_call [] 11 ^success_call 21 [^success_n; ^success_n] ^success_body []
    (BoundAtom (AstId 10)) = NONE ∧
  try_call [] 11 ^success_call 21
    [^success_n; ^success_b with var_scope := 0] ^success_body []
    (BoundAtom (AstId 10)) = NONE
Proof
  EVAL_TAC
QED

Theorem try_success_omitted_keeps_full_result_positions:
  try_call [] 11 ^success_call 21 [] ^success_body []
    (BoundAtom (AstId 10)) =
  SOME ([DefineStmt (AstId 11) (SingleType BoolT)
           (TupleComponentOperation 0 (BoundAtom (AstId 10)));
         DefineStmt (AstId 12) (SingleType (UintT 256))
           (TupleComponentOperation 1 (BoundAtom (AstId 10)));
         DefineStmt (AstId 13) (SingleType BoolT)
           (TupleComponentOperation 2 (BoundAtom (AstId 10)));
         DefineStmt (AstId 14) RevertDataType
           (TupleComponentOperation 3 (BoundAtom (AstId 10)))],
        BoundAtom (AstId 11), [], BoundAtom (AstId 14), 15)
Proof
  EVAL_TAC
QED

Theorem try_success_only_named_components_bound:
  case elab_stmt
         (^ctx0 with variables := [(40, AddressT NonpayableAddress)]) 10
         (SrcTryStatement ^(at 19) ^success_call ^(at 21)
            [^success_n; ^success_b] ^success_body
            [SrcCatchClause ^(at 23) GenericCatch [] (SrcBlock ^(at 24) [])]) of
    INL ((ss, _), _) =>
      (case LAST ss of
         IfStmt _ ds _ =>
           ds = [DefineStmt (AstId 4) (SingleType (UintT 256))
                   (ConvertOperation (UintT 256) (BoundAtom (AstId 12)))]
       | _ => F)
  | _ => F
Proof
  EVAL_TAC
QED

(* Two independently bad operands of each operand list are both reported,
 * each under its own id, beside the node's own blocker if it has one: string
 * literals that convert to no number, number literals that a packed encoding
 * rejects, and unsupported expressions. *)
fun string_at id = “SrcLiteral ^(at id) StringLiteral "a" "t_stringliteral_a"”;
fun one_at id = “SrcLiteral ^(at id) NumberLiteral "1" "t_rational_1_by_1"”;
fun bad_at id = “SrcUnsupportedExpr ^(at id) "bad" []”;
fun reports r bs =
  list_mk_conj (map (fn b => “MEM ^b (blockers ^r)”) bs);
val string_32_33 = [“(32, "string literal conversion")”, “(33, "string literal conversion")”];
val bad_32_33 = [“(32, "bad")”, “(33, "bad")”];

Theorem modular_operands_all_report:
  ^(reports “elab_expr ^ctx0 10
               (SrcModular ^(at 30) ^(at 31) AddModOp
                  [^(string_at 32); ^(string_at 33); ^(one_at 34)] "t_uint256")”
     string_32_33)
Proof
  EVAL_TAC
QED

Theorem ecrecover_operands_all_report:
  ^(reports “elab_expr ^ctx0 10
               (SrcBuiltinOperation ^(at 30) (SOME ^(at 31)) EcrecoverBuiltin
                  [SrcLiteral ^(at 32) StringLiteral
                     "0123456789abcdef0123456789abcdef0" "t_stringliteral_x";
                   ^(one_at 34);
                   SrcLiteral ^(at 33) StringLiteral
                     "0123456789abcdef0123456789abcdef0" "t_stringliteral_x";
                   ^(one_at 35)]
                  "t_address")”
     string_32_33)
Proof
  EVAL_TAC
QED

Theorem abi_encode_operands_all_report:
  ^(reports “elab_expr ^ctx0 10
               (SrcAbiEncode ^(at 30) ^(at 31) AbiPacked [^(one_at 32); ^(one_at 33)]
                  "t_bytes_memory_ptr")”
     [“(32, "packed encoding of a number literal")”,
      “(33, "packed encoding of a number literal")”])
Proof
  EVAL_TAC
QED

Theorem abi_encode_function_array_refused:
  elab_expr (^ctx0 with variables :=
      [(40, LocatedT MemoryLoc (ArrayT
             (FunctionT InternalFn PureMut [UintT 256] [UintT 256]) NONE))]) 10
    (SrcAbiEncode ^(at 30) ^(at 31) AbiPlain
      [SrcIdentifier ^(at 32) "fns" 40
         "t_array$_t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_$dyn_memory_ptr"]
      "t_bytes_memory_ptr") =
  INR [(30, "abi encoding of this type")]
Proof
  EVAL_TAC
QED

Theorem abi_encode_function_fixed_array_packed_refused:
  elab_expr (^ctx0 with variables :=
      [(40, LocatedT MemoryLoc (ArrayT
             (FunctionT InternalFn PureMut [UintT 256] [UintT 256]) (SOME 2)))]) 10
    (SrcAbiEncode ^(at 30) ^(at 31) AbiPacked
      [SrcIdentifier ^(at 32) "fns" 40
         "t_array$_t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_$2_memory_ptr"]
      "t_bytes_memory_ptr") =
  INR [(32, "abi encoding of this type")]
Proof
  EVAL_TAC
QED

(* A recursive memory object is unsupported even when referenced only by a
 * function signature in a struct field. A signature pointing back to its
 * own struct does not make the struct's memory layout recursive. *)
Theorem struct_function_signatures_checked:
  contract_type_blockers
    [(AstId 40, StructDeclaration [(AstId 41, ArrayT (StructT (AstId 40)) NONE)]);
     (AstId 42, StructDeclaration [(AstId 43,
       FunctionT InternalFn PureMut [LocatedT MemoryLoc (StructT (AstId 40))] [])]);
     (AstId 44, StructDeclaration [(AstId 45,
       FunctionT InternalFn PureMut [LocatedT MemoryLoc (StructT (AstId 44))] [])])]
    [] [] [] = [(42, "unsupported type declaration")]
Proof
  EVAL_TAC
QED

val uses_missing_struct =
  “"t_function_external_view$_t_struct$_S_$40_memory_ptr_$returns$__$"”;

Theorem external_function_value_signature_checked:
  IS_SOME (function_type_identifier ^uses_missing_struct) ∧
  elab_expr ^ctx0 10
    (SrcExternalFunction ^(at 30) (SrcEnvironment ^(at 31) SelfAddress "t_address")
       [1w; 2w; 3w; 4w] ^uses_missing_struct) =
  INR [(30, "unsupported external function signature")]
Proof
  EVAL_TAC
QED

Theorem binary_operands_all_report:
  ^(reports “elab_expr ^ctx0 10
               (SrcBinaryOperation ^(at 30) SrcAdd ^(string_at 32) ^(string_at 33)
                  "t_uint256" "t_uint256")”
     string_32_33) ∧
  ^(reports “elab_expr ^ctx0 10
               (SrcBinaryOperation ^(at 30) SrcAnd ^(string_at 32) ^(string_at 33)
                  "t_bool" "t_bool")”
     string_32_33)
Proof
  EVAL_TAC
QED

Theorem builtin_operands_all_report:
  ^(reports “elab_expr ^ctx0 10
               (SrcBuiltinCall ^(at 30) ^(at 31) RequireBuiltin
                  (SOME ^(bad_at 32)) (SOME ^(bad_at 33)) "t_bool")”
     (“(30, "unsupported builtin call")” :: bad_32_33))
Proof
  EVAL_TAC
QED

val two_parameters = function_of “[^supported_y; ^supported_y]” “[] : src_variable list” “[] : src_stmt list”;

Theorem internal_call_operands_all_report:
  ^(reports “elab_expr (^ctx0 with functions := [(1, ^two_parameters)]) 10
               (SrcFunctionCall ^(at 30) F (SrcIdentifier ^(at 31) "f" 1 "t_function")
                  [^(string_at 32); ^(string_at 33)] [] "t_tuple$__$")”
     string_32_33)
Proof
  EVAL_TAC
QED

Theorem external_call_operands_all_report:
  ^(reports “elab_expr ^ctx0 10
               (SrcExternalCall ^(at 30)
                  <| ext_selector := [0w; 0w; 0w; 0w]; ext_mutability := NonpayableMut; ext_kind := ExternalCall; ext_bound := F;
                     ext_signature := FunctionSignature [] [] |>
                  [] [^(bad_at 32); ^(bad_at 33)] [] "t_tuple$__$")”
     (“(30, "unsupported external call")” :: bad_32_33))
Proof
  EVAL_TAC
QED

Theorem statement_operands_all_report:
  ^(reports “elab_stmt ^ctx0 10 (SrcEmit ^(at 30) 5 [^(bad_at 32); ^(bad_at 33)] [])”
     (“(30, "unknown event")” :: bad_32_33)) ∧
  ^(reports “elab_stmt ^ctx0 10
               (SrcRevertError ^(at 30)
                  <| error_selector := [0w; 0w; 0w; 0w]; error_parameters := [] |>
                  [^(bad_at 32); ^(bad_at 33)] [])”
     (“(30, "revert does not match the error")” :: bad_32_33)) ∧
  ^(reports “elab_stmt (^ctx0 with <| returns := [(1, UintT 256); (2, UintT 256)];
                                      returns_id := 3 |>) 10
                (SrcReturn ^(at 30) 3
                   (SOME (SrcTupleExpression ^(at 31)
                            [SOME ^(string_at 32); SOME ^(string_at 33)]
                            "t_tuple$_t_uint256_$_t_uint256_$")))”
     string_32_33)
Proof
  EVAL_TAC
QED

(* A node whose sibling operands fail differently still reports both: one
 * operand fails to elaborate (32 or 33), another elaborates and fails to
 * convert. *)
val mixed_string = [“(32, "string literal conversion")”, “(33, "bad")”];

Theorem modular_mixed_operands_report:
  ^(reports “elab_expr ^ctx0 10
               (SrcModular ^(at 30) ^(at 31) AddModOp
                  [^(string_at 32); ^(bad_at 33); ^(one_at 34)] "t_uint256")”
     mixed_string)
Proof
  EVAL_TAC
QED

Theorem ecrecover_mixed_operands_report:
  ^(reports “elab_expr ^ctx0 10
               (SrcBuiltinOperation ^(at 30) (SOME ^(at 31)) EcrecoverBuiltin
                  [SrcLiteral ^(at 32) StringLiteral
                     "0123456789abcdef0123456789abcdef0" "t_stringliteral_x";
                   ^(one_at 34); ^(bad_at 33); ^(one_at 35)]
                  "t_address")”
     mixed_string)
Proof
  EVAL_TAC
QED

Theorem abi_encode_mixed_operands_report:
  ^(reports “elab_expr ^ctx0 10
               (SrcAbiEncode ^(at 30) ^(at 31) AbiPacked [^(one_at 32); ^(bad_at 33)]
                  "t_bytes_memory_ptr")”
     [“(32, "packed encoding of a number literal")”, “(33, "bad")”])
Proof
  EVAL_TAC
QED

Theorem abi_selector_mixed_operands_report:
  ^(reports “elab_expr ^ctx0 10
               (SrcAbiEncode ^(at 30) ^(at 31) AbiWithSelector
                  [SrcLiteral ^(at 32) StringLiteral
                     "0123456789abcdef0123456789abcdef0" "t_stringliteral_x";
                   ^(bad_at 33)]
                  "t_bytes_memory_ptr")”
     [“(32, "selector not a bytes4")”, “(33, "bad")”])
Proof
  EVAL_TAC
QED

(* A literal signature's selector is computed when elaborating, as the
 * compiler does; a signature that is not a string is reported with the
 * arguments' blockers, and one that is missing is reported on the node. *)
Theorem abi_signature_literal_is_constant_selector:
  elab_expr ^ctx0 10
    (SrcAbiEncode ^(at 30) ^(at 31) AbiWithSignature
       [SrcLiteral ^(at 32) StringLiteral "f()" "t_stringliteral_f"]
       "t_bytes_memory_ptr") =
  INL (([DefineStmt (AstId 10) (SingleType (LocatedT MemoryLoc BytesT))
           (AbiEncodeOperation
              (SOME (ConstantAtom (BytesValue (TAKE 4 (Keccak_256_w64
                 (MAP (n2w o ORD) "f()")))))) [] [])],
        BoundAtom (AstId 10), ElabType (LocatedT MemoryLoc BytesT)), 11)
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [“Keccak_256_w64”])
QED

Theorem abi_signature_not_string_reports:
  ^(reports “elab_expr ^ctx0 10
               (SrcAbiEncode ^(at 30) ^(at 31) AbiWithSignature
                  [^(one_at 32); ^(bad_at 33)] "t_bytes_memory_ptr")”
     [“(32, "signature not a string")”, “(33, "bad")”]) ∧
  ^(reports “elab_expr ^ctx0 10
               (SrcAbiEncode ^(at 30) ^(at 31) AbiWithSignature [] "t_bytes_memory_ptr")”
     [“(30, "missing signature")”])
Proof
  EVAL_TAC
QED

(* A selector that fails to elaborate next to an argument that fails to
 * convert: both are reported. *)
Theorem abi_selector_failure_reports_arguments:
  ^(reports “elab_expr ^ctx0 10
               (SrcAbiEncode ^(at 30) ^(at 31) AbiWithSelector
                  [^(bad_at 32);
                   SrcLiteral ^(at 33) NumberLiteral "0.5" "t_rational_1_by_2"]
                  "t_bytes_memory_ptr")”
     [“(32, "bad")”, “(33, "abi encoding of this type")”]) ∧
  ^(reports “elab_expr ^ctx0 10
               (SrcAbiEncode ^(at 30) ^(at 31) (AbiCall ["t_bool"])
                  [^(bad_at 32); ^(string_at 33)] "t_bytes_memory_ptr")”
     [“(32, "bad")”, “(33, "string literal conversion")”])
Proof
  EVAL_TAC
QED

(* A call that names its arguments converts each to its own parameter's type:
 * with the parameters (uint256, bytes1) taken in the order [1; 0], the string
 * literal is converted to uint256 in the first call and to bytes1 in the
 * second, where it converts. *)
Theorem named_call_mixed_operands_report:
  ^(reports “elab_args ^ctx0 10 30 0 [1; 0] [ValueOf (UintT 256); ValueOf (FixedBytesT 1)]
               [^(bad_at 32); ^(string_at 33)]”
     [“(32, "bad")”, “(33, "string literal conversion")”]) ∧
  ¬MEM (32, "string literal conversion")
     (blockers (elab_args ^ctx0 10 30 0 [1; 0] [ValueOf (UintT 256); ValueOf (FixedBytesT 1)]
                  [^(string_at 32); ^(bad_at 33)])) ∧
  MEM (33, "bad")
     (blockers (elab_args ^ctx0 10 30 0 [1; 0] [ValueOf (UintT 256); ValueOf (FixedBytesT 1)]
                  [^(string_at 32); ^(bad_at 33)]))
Proof
  EVAL_TAC
QED

Theorem abi_call_mixed_operands_report:
  ^(reports “elab_expr ^ctx0 10
               (SrcAbiEncode ^(at 30) ^(at 31) (AbiCall ["t_bad"])
                  [^(string_at 32); ^(bad_at 33)] "t_bytes_memory_ptr")”
     [“(30, "abi encoding of this type")”, “(33, "bad")”])
Proof
  EVAL_TAC
QED

(* The arguments after an attached one, whose elaboration (first) or
 * conversion (second) fails. *)
Theorem attached_call_mixed_operands_report:
  ^(reports “elab_args ^ctx0 10 30 1 [] [ValueOf (UintT 256); ValueOf (UintT 256)]
               [^(bad_at 32); ^(string_at 33)]”
     [“(32, "bad")”, “(33, "string literal conversion")”]) ∧
  ^(reports “elab_args ^ctx0 10 30 1 [] [ValueOf (UintT 256); ValueOf (UintT 256)]
               [^(string_at 32); ^(bad_at 33)]”
     [“(32, "string literal conversion")”, “(33, "bad")”])
Proof
  EVAL_TAC
QED

(* A call whose argument order isn't a permutation, or that has more
 * arguments than parameters, still reports every failing argument. *)
Theorem malformed_call_operands_report:
  ^(reports “elab_args ^ctx0 10 30 0 [0; 0] [ValueOf (UintT 256); ValueOf (UintT 256)]
               [^(string_at 32); ^(bad_at 33)]”
     [“(32, "string literal conversion")”, “(33, "bad")”]) ∧
  ^(reports “elab_args ^ctx0 10 30 0 [0; 0] [ValueOf (UintT 256); ValueOf (UintT 256)]
               [^(one_at 32); ^(bad_at 33)]”
     [“(33, "bad")”]) ∧
  ^(reports “elab_args ^ctx0 10 30 2 [] [ValueOf (UintT 256)]
               [^(bad_at 32); ^(bad_at 33)]”
     bad_32_33) ∧
  ^(reports “elab_args ^ctx0 10 30 1 [1; 0] [ValueOf (UintT 256); ValueOf (UintT 256)]
               [^(bad_at 32); ^(bad_at 33)]”
     (“(30, "argument order")” :: bad_32_33))
Proof
  EVAL_TAC
QED

Theorem internal_call_mixed_operands_report:
  ^(reports “elab_expr (^ctx0 with functions := [(1, ^two_parameters)]) 10
               (SrcFunctionCall ^(at 30) F (SrcIdentifier ^(at 31) "f" 1 "t_function")
                  [^(string_at 32); ^(bad_at 33)] [] "t_tuple$__$")”
     mixed_string)
Proof
  EVAL_TAC
QED

Theorem external_call_mixed_operands_report:
  ^(reports “elab_expr ^ctx0 10
               (SrcExternalCall ^(at 30)
                  <| ext_selector := [0w; 0w; 0w; 0w]; ext_mutability := NonpayableMut; ext_kind := ExternalCall; ext_bound := F;
                     ext_signature := FunctionSignature [^supported_y; ^supported_y] [] |>
                  [] [^(bad_at 33); ^(string_at 32); ^(one_at 34)] [] "t_tuple$__$")”
     mixed_string)
Proof
  EVAL_TAC
QED

(* The members of a dynamic storage array that the elaborator doesn't take
 * still report their arguments. *)
val array_ctx = “^ctx0 with state := [(5, ArrayT (UintT 256) NONE)]”;
fun array_call member args order =
  “SrcFunctionCall ^(at 30) F
     (SrcArrayMember ^(at 31) ^member
        (SrcIdentifier ^(at 35) "a" 5 "t_array$_t_uint256_$dyn_storage") "t_function")
     ^args ^order "t_tuple$__$"”;
val array_reports = [“(30, "unsupported array member call")”, “(32, "bad")”];

Theorem array_member_arguments_report:
  ^(reports “elab_expr ^array_ctx 10
               ^(array_call “"pop"” “[^(bad_at 32)]” “[] : num list”)”
     array_reports) ∧
  ^(reports “elab_expr ^array_ctx 10
               ^(array_call “"push"” “[^(bad_at 32); ^(bad_at 33)]” “[] : num list”)”
     (“(33, "bad")” :: array_reports)) ∧
  ^(reports “elab_expr ^array_ctx 10
               ^(array_call “"push"” “[^(bad_at 32)]” “[0]”)”
     array_reports)
Proof
  EVAL_TAC
QED

(* Each level of a deep nesting of rejected operand lists reports its own
 * failing operand, and the innermost one is reported once. The operands are
 * elaborated in one pass: elaborating a rejected list's operands again to
 * report them would visit the innermost one 2^30 times. *)
fun nested_modular 0 = bad_at 1000
  | nested_modular k =
      “SrcModular ^(at (1000 + 4 * k)) ^(at (1001 + 4 * k)) AddModOp
         [^(nested_modular (k - 1)); ^(string_at (1002 + 4 * k)); ^(one_at (1003 + 4 * k))]
         "t_uint256"”;
val nested_reports =
  listSyntax.mk_list
    (“(1000, "bad")” ::
     List.tabulate (30, fn k =>
       “(^(numSyntax.term_of_int (1006 + 4 * k)), "string literal conversion")”),
     “:num # string”);

val nested_reported = EVAL “blockers (elab_expr ^ctx0 10 ^(nested_modular 30))”;

Theorem nested_rejected_operands_report:
  blockers (elab_expr ^ctx0 10 ^(nested_modular 30)) = ^nested_reports
Proof
  REWRITE_TAC [nested_reported]
QED

(* The unit elaborates, so nothing in it fails. *)
Theorem pure_core_has_no_failures:
  unit_elaboration_failures T pure_core = []
Proof
  CONV_TAC cv_eval
QED

Theorem literal_bytes_width_checked:
  coerce 0 (FixedBytesT 2) (ConstantAtom (BytesValue [0x61w; 0x62w; 0x63w]))
    ElabBytesLiteral = INR "string literal conversion" ∧
  coerce 0 (FixedBytesT 0) (ConstantAtom (BytesValue [])) ElabBytesLiteral = INR "string literal conversion" ∧
  coerce 0 (FixedBytesT 33) (ConstantAtom (BytesValue [])) ElabBytesLiteral = INR "string literal conversion" ∧
  coerce 0 (FixedBytesT 0) (ConstantAtom (IntegerValue 0)) ElabLiteral = INR "number literal conversion" ∧
  coerce 0 (FixedBytesT 33) (ConstantAtom (IntegerValue 0)) ElabLiteral = INR "number literal conversion"
Proof
  EVAL_TAC
QED

(* Edited units of solidityImportTest that pass valid_src_unit but whose
 * edited function fails elaboration, which checks it against the compiler's
 * annotations: preparation marks it unsupported. *)

(* an identifier naming no declaration *)
Theorem dangling_reference_fails_elaboration:
  unit_elaboration_failures T dangling_reference ≠ []
Proof
  CONV_TAC cv_eval
QED

(* an identifier annotated with another type than its variable's *)
Theorem identifier_type_mismatch_fails_elaboration:
  unit_elaboration_failures T identifier_type_mismatch ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a comparison annotated with another type than bool *)
Theorem comparison_type_mismatch_fails_elaboration:
  unit_elaboration_failures T comparison_type_mismatch ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a function used as a value *)
Theorem function_as_value_fails_elaboration:
  unit_elaboration_failures T function_as_value ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a declaration statement whose assignments do not list its declaration *)
Theorem unlinked_declaration_fails_elaboration:
  unit_elaboration_failures T unlinked_declaration ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a call with fewer arguments than parameters *)
Theorem call_arity_fails_elaboration:
  unit_elaboration_failures T call_arity ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a pure function using a state variable *)
Theorem pure_writes_state_fails_elaboration:
  unit_elaboration_failures T pure_writes_state ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a mapping read annotated with another value type *)
Theorem mapping_leaf_metadata_mismatch_fails_elaboration:
  unit_elaboration_failures T mapping_leaf_metadata_mismatch ≠ []
Proof
  CONV_TAC cv_eval
QED

(* an array read annotated with another element type *)
Theorem array_leaf_mismatch_fails_elaboration:
  unit_elaboration_failures T array_leaf_mismatch ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a require message that is not a literal *)
Theorem nonliteral_builtin_message_fails_elaboration:
  unit_elaboration_failures T nonliteral_builtin_message ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a struct member naming no member *)
Theorem struct_field_identity_mismatch_fails_elaboration:
  unit_elaboration_failures T struct_field_identity_mismatch ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a struct member annotated with another type *)
Theorem struct_field_type_mismatch_fails_elaboration:
  unit_elaboration_failures T struct_field_type_mismatch ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a call reaching no implemented function *)
Theorem unresolved_override_fails_elaboration:
  unit_elaboration_failures T unresolved_override ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a conditional over storage references *)
Theorem storage_conditional_fails_elaboration:
  unit_elaboration_failures T storage_conditional ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a conditional over stored bytes *)
Theorem stored_bytes_conditional_fails_elaboration:
  unit_elaboration_failures T stored_bytes_conditional ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a conditional over tuples *)
Theorem tuple_conditional_fails_elaboration:
  unit_elaboration_failures T tuple_conditional ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a conditional over calldata references *)
Theorem calldata_conditional_fails_elaboration:
  unit_elaboration_failures T calldata_conditional ≠ []
Proof
  CONV_TAC cv_eval
QED

(* a conditional over functions *)
Theorem function_conditional_fails_elaboration:
  unit_elaboration_failures T function_conditional ≠ []
Proof
  CONV_TAC cv_eval
QED

Theorem address_literal_bounds_checked:
  elab_expr ^ctx0 10
    (SrcLiteral ^(at 30) NumberLiteral
       "1461501637330902918203684832716283019655932542976" "t_address") =
    INR [(30, "unsupported literal")] ∧
  elab_expr ^ctx0 10
    (SrcLiteral ^(at 30) NumberLiteral "-1" "t_address") =
    INR [(30, "unsupported literal")]
Proof
  EVAL_TAC
QED

Theorem delete_readonly_and_storage_pointer_fail_in_elaboration:
  EVERY (λty. ISR (finish_delete ctx 1 [] (LocalDestination 2 ty) 3))
    [LocatedT CalldataLoc BytesT; LocatedT StorageLoc BytesT;
     MappingT (UintT 256) (UintT 256)]
Proof
  EVAL_TAC
QED
