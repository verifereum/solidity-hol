(* The importer's read of the pinned compiler's own Yul, and the negative
 * fixtures it fails closed on. See syntax/yulImportLib.sml.
 *)
Theory yulImportTest
Ancestors
  yulAST yulDialect yulState yulEvaluator cv_string_fmap vfmCompute
Libs
  yulImportLib cv_transLib wordsLib

(* Read by holbuild's dependency scanner, which stages the fixture. *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [
  "../testdata/yul/expected/shadowed_builtins.json",
  "../testdata/yul/expected/shadowed_builtins-optimized.json",
  "../testdata/differential/shadowed_builtins.sol"
]

val fixture = "../testdata/yul/expected/shadowed_builtins.json"
val optimized_fixture = "../testdata/yul/expected/shadowed_builtins-optimized.json"
val source = "testdata/differential/shadowed_builtins.sol"
val contract = "ShadowedBuiltins"

Definition shadowed_builtins_ir_def:
  shadowed_builtins_ir =
    ^(yulImportLib.import_runtime_artifact fixture source contract
        yulImportLib.Ir)
End

Definition shadowed_builtins_ir_optimized_def:
  shadowed_builtins_ir_optimized =
    ^(yulImportLib.import_runtime_artifact fixture source contract
        yulImportLib.IrOptimized)
End

Definition shadowed_builtins_optimized_def:
  shadowed_builtins_optimized =
    ^(yulImportLib.import_runtime_artifact optimized_fixture source contract
        yulImportLib.IrOptimized)
End

(* A smoke run of the imported runtime through the compiler's own dispatcher:
 * the corpus case shadowed_true, whose calldata is run(bool)'s selector
 * followed by the ABI word for true.
 *)
val () = cv_auto_trans shadowed_builtins_ir_def;

Definition probe_call_data_def:
  probe_call_data =
    [0x16w; 0x6Aw; 0x2Aw; 0xD5w] ++ REPLICATE 31 (0w : word8) ++ [0x01w]
End

val () = cv_auto_trans probe_call_data_def;

Definition probe_machine_def:
  probe_machine =
    <| accounts := empty_accounts; logs := []; self_address := 0x1000w;
       call_value := 0w; call_data := probe_call_data; memory := FEMPTY;
       memory_size := 0; scopes := [] |>
End

val () = cv_auto_trans probe_machine_def;

val probe = cv_eval “(run_yul 200000 shadowed_builtins_ir probe_machine).completion”;
val probe_completion = rhs (concl probe);
val () = print ("PROBE-COMPLETION: " ^
  (case strip_comb probe_completion of
     (f, [bytes]) =>
       fst (dest_const f) ^ " " ^
       String.concat (map (fn b =>
         StringCvt.padLeft #"0" 2
           (String.map Char.toLower
              (Arbnum.toHexString (wordsSyntax.dest_word_literal b))))
         (fst (listSyntax.dest_list bytes)))
   | _ => term_to_string probe_completion) ^ "\n");
val probe_reverts = cv_eval “(run_yul 200000 shadowed_builtins_ir probe_machine).machine.accounts”;
val () = print ("PROBE-ACCOUNTS-SIZE: " ^
  Int.toString (term_size (rhs (concl probe_reverts))) ^ "\n");
