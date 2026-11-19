(* Smoke tests for the pure evaluator, run by cv_eval. The semantics test set
 * is solidityCoreProgramsTest.
 *)
Theory solidityEvaluatorTest
Ancestors
  solidityEvaluator solidityEntry
Libs
  cv_transLib wordsLib intLib

Overload u8 = “UintT 8”
Overload u256 = “UintT 256”
Overload k = “λi. ConstantAtom (IntegerValue i)”

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
    memory := FEMPTY |+ (0x5F, 0x80w); memory_size := 96;
    immutables := SOME FEMPTY;
    targets := FEMPTY; return_data := SOME []
  |>
End

(* add(x, y) returns (r): checked uint8 addition. *)
Definition add_proc_def:
  add_proc = <|
    procedure_id := AstId 1;
    parameters := [(AstId 10, u8); (AstId 11, u8)];
    return_bindings := [(AstId 12, u8)];
    body := [
      DefineStmt (AstId 13) (SingleType u8)
        (ScalarOperation u8 CheckedArithmetic AddOp
           [BoundAtom (AstId 10); BoundAtom (AstId 11)]);
      ReturnStmt [BoundAtom (AstId 13)]]
  |>
End

(* sum(n) returns (acc): adds 1..n, breaking after 5; the loop body writes the
 * enclosing i and acc, and the condition prelude reruns every iteration.
 *)
Definition sum_proc_def:
  sum_proc = <|
    procedure_id := AstId 2;
    parameters := [(AstId 20, u256)];
    return_bindings := [(AstId 21, u256)];
    body := [
      DefineStmt (AstId 22) (SingleType u256) (ConvertOperation u256 (k 0));
      WhileStmt
        [DefineStmt (AstId 23) (SingleType BoolT)
           (ScalarOperation u256 UncheckedArithmetic LessThanOp
              [BoundAtom (AstId 22); BoundAtom (AstId 20)])]
        (BoundAtom (AstId 23))
        [DefineStmt (AstId 24) (SingleType u256)
           (ScalarOperation u256 CheckedArithmetic AddOp
              [BoundAtom (AstId 22); k 1]);
         CaptureBindingStmt (AstId 25) (AstId 22);
         WriteScalarStmt (AstId 25) u256 (BoundAtom (AstId 24));
         DefineStmt (AstId 26) (SingleType u256)
           (ScalarOperation u256 CheckedArithmetic AddOp
              [BoundAtom (AstId 21); BoundAtom (AstId 24)]);
         CaptureBindingStmt (AstId 27) (AstId 21);
         WriteScalarStmt (AstId 27) u256 (BoundAtom (AstId 26));
         DefineStmt (AstId 28) (SingleType BoolT)
           (ScalarOperation u256 UncheckedArithmetic EqualOp
              [BoundAtom (AstId 24); k 5]);
         IfStmt (BoundAtom (AstId 28)) [BreakStmt] [ContinueStmt]]]
  |>
End

(* fact(n): recursion, falling through to the return binding on n = 0. *)
Definition fact_proc_def:
  fact_proc = <|
    procedure_id := AstId 3;
    parameters := [(AstId 30, u256)];
    return_bindings := [(AstId 31, u256)];
    body := [
      DefineStmt (AstId 32) (SingleType BoolT)
        (ScalarOperation u256 UncheckedArithmetic EqualOp
           [BoundAtom (AstId 30); k 0]);
      IfStmt (BoundAtom (AstId 32))
        [ReturnStmt [k 1]]
        [DefineStmt (AstId 33) (SingleType u256)
           (ScalarOperation u256 CheckedArithmetic SubtractOp
              [BoundAtom (AstId 30); k 1]);
         DefineStmt (AstId 34) (SingleType u256)
           (InternalCallOperation (AstId 3) [BoundAtom (AstId 33)]);
         DefineStmt (AstId 35) (SingleType u256)
           (ScalarOperation u256 CheckedArithmetic MultiplyOp
              [BoundAtom (AstId 30); BoundAtom (AstId 34)]);
         ReturnStmt [BoundAtom (AstId 35)]]]
  |>
End

(* pair() returns (uint256, bool); first() destructures it. *)
Definition pair_proc_def:
  pair_proc = <|
    procedure_id := AstId 4;
    parameters := [];
    return_bindings := [(AstId 40, u256); (AstId 41, BoolT)];
    body := [ReturnStmt [k 7; ConstantAtom (BoolValue T)]]
  |>
End

Definition first_proc_def:
  first_proc = <|
    procedure_id := AstId 5;
    parameters := [];
    return_bindings := [(AstId 50, u256)];
    body := [
      DefineStmt (AstId 51) (ProductType [SingleType u256; SingleType BoolT])
        (InternalCallOperation (AstId 4) []);
      DefineStmt (AstId 52) (SingleType u256)
        (TupleComponentOperation 0 (BoundAtom (AstId 51)));
      ReturnStmt [BoundAtom (AstId 52)]]
  |>
End

Definition spin_proc_def:
  spin_proc = <|
    procedure_id := AstId 6;
    parameters := [];
    return_bindings := [];
    body := [WhileStmt [] (ConstantAtom (BoolValue T)) []]
  |>
End

(* A revert from a nested call carries its bytes out. *)
Definition fail_proc_def:
  fail_proc = <|
    procedure_id := AstId 7;
    parameters := [];
    return_bindings := [];
    body := [RevertStmt (ConstantAtom (BytesValue [0x01w; 0x02w]))]
  |>
End

Definition call_fail_proc_def:
  call_fail_proc = <|
    procedure_id := AstId 8;
    parameters := [];
    return_bindings := [(AstId 80, u256)];
    body := [
      DefineStmt (AstId 81) (ProductType []) (InternalCallOperation (AstId 7) []);
      ReturnStmt [k 1]]
  |>
End

(* The caller captures target 90 before a call whose callee reuses id 90;
 * the caller's target map must survive the call.
 *)
Definition callee_proc_def:
  callee_proc = <|
    procedure_id := AstId 9;
    parameters := [];
    return_bindings := [(AstId 91, u256)];
    body := [
      DefineStmt (AstId 92) (SingleType u256) (ConvertOperation u256 (k 9));
      CaptureBindingStmt (AstId 90) (AstId 91);
      WriteScalarStmt (AstId 90) u256 (BoundAtom (AstId 92))]
  |>
End

Definition caller_proc_def:
  caller_proc = <|
    procedure_id := AstId 100;
    parameters := [];
    return_bindings := [(AstId 101, u256)];
    body := [
      CaptureBindingStmt (AstId 90) (AstId 101);
      DefineStmt (AstId 102) (SingleType u256)
        (InternalCallOperation (AstId 9) []);
      WriteScalarStmt (AstId 90) u256 (BoundAtom (AstId 102))]
  |>
End

Definition test_program_def:
  test_program = <|
    unsupported_procedures := []; procedures := [add_proc; sum_proc; fact_proc; pair_proc; first_proc;
                   spin_proc; fail_proc; call_fail_proc; callee_proc;
                   caller_proc];
    struct_layouts := []; function_ids := []; type_declarations := [];
    state_variables := []; immutables := [];
    entry_procedure := AstId 1;
    external_functions := []; receive_procedure := NONE;
    fallback_procedure := NONE; creation_procedure := NONE
  |>
End

Definition test_env_def:
  test_env = core_program_environment test_program
End

Theorem test_program_wf:
  wf_core_program test_env test_program
Proof
  EVAL_TAC
QED

Definition run_def:
  run fuel f args = (invoke_source fuel test_env f args initial_state []).completion
End

val () = cv_auto_trans run_def;

Theorem add_ok:
  run 10 (AstId 1) [ScalarValue (IntegerValue 2); ScalarValue (IntegerValue 3)] =
  ReturnCompletion [ScalarValue (IntegerValue 5)]
Proof
  CONV_TAC cv_eval
QED

Theorem add_overflow_panics:
  run 10 (AstId 1) [ScalarValue (IntegerValue 255); ScalarValue (IntegerValue 1)] =
  PanicCompletion 0x11
Proof
  CONV_TAC cv_eval
QED

Theorem sum_runs_to_completion:
  run 10 (AstId 2) [ScalarValue (IntegerValue 3)] =
  ReturnCompletion [ScalarValue (IntegerValue 6)]
Proof
  CONV_TAC cv_eval
QED

Theorem sum_breaks:
  run 10 (AstId 2) [ScalarValue (IntegerValue 100)] =
  ReturnCompletion [ScalarValue (IntegerValue 15)]
Proof
  CONV_TAC cv_eval
QED

Theorem fact_recursion:
  run 10 (AstId 3) [ScalarValue (IntegerValue 5)] =
  ReturnCompletion [ScalarValue (IntegerValue 120)]
Proof
  CONV_TAC cv_eval
QED

Theorem deep_recursion_exhausts_fuel:
  run 3 (AstId 3) [ScalarValue (IntegerValue 5)] = FuelExhausted
Proof
  CONV_TAC cv_eval
QED

Theorem multiple_returns:
  run 10 (AstId 5) [] = ReturnCompletion [ScalarValue (IntegerValue 7)]
Proof
  CONV_TAC cv_eval
QED

Theorem infinite_loop_exhausts_fuel:
  run 20 (AstId 6) [] = FuelExhausted
Proof
  CONV_TAC cv_eval
QED

Theorem nested_revert:
  run 10 (AstId 8) [] = RevertCompletion [0x01w; 0x02w]
Proof
  CONV_TAC cv_eval
QED

Theorem caller_targets_survive_call:
  run 10 (AstId 100) [] = ReturnCompletion [ScalarValue (IntegerValue 9)]
Proof
  CONV_TAC cv_eval
QED

(* Storage: store(x) writes the uint8 state variable 200, at byte 1 of slot
 * 0, and returns it read back. *)

Definition counter_def:
  counter = <| state_id := AstId 200; state_type := u8; state_backend := PersistentStorage; state_slot := 0w;
               state_offset := 1 |>
End

Definition store_proc_def:
  store_proc = <|
    procedure_id := AstId 20;
    parameters := [(AstId 21, u8)];
    return_bindings := [(AstId 22, u8)];
    body := [
      DefineStmt (AstId 25) (ReferenceType u8) (StateReferenceOperation (AstId 200));
      CaptureValueStmt (AstId 23) (BoundAtom (AstId 25));
      WriteScalarStmt (AstId 23) u8 (BoundAtom (AstId 21));
      DefineStmt (AstId 24) (SingleType u8) (ReadOperation u8 (BoundAtom (AstId 25)));
      ReturnStmt [BoundAtom (AstId 24)]]
  |>
End

Definition storage_program_def:
  storage_program vs = <|
    unsupported_procedures := []; procedures := [store_proc];
    struct_layouts := []; function_ids := []; type_declarations := [];
    state_variables := vs; immutables := [];
    entry_procedure := AstId 20;
    external_functions := []; receive_procedure := NONE;
    fallback_procedure := NONE; creation_procedure := NONE
  |>
End

Definition storage_wf_def:
  storage_wf vs ⇔
    wf_core_program (core_program_environment (storage_program vs))
      (storage_program vs)
End

Theorem storage_program_wf:
  storage_wf [counter]
Proof
  EVAL_TAC
QED

(* A variable that overruns its slot, one declared twice, and an undeclared
 * one are rejected. *)
Theorem storage_program_not_wf:
  ¬storage_wf [counter with state_offset := 32] ∧
  ¬storage_wf [counter; counter] ∧
  ¬storage_wf []
Proof
  EVAL_TAC
QED

Definition static_state_def:
  static_state =
    initial_state with frame := initial_state.frame with static_context := T
End

Definition run_store_def:
  run_store st x =
    (invoke_source 10 (core_program_environment (storage_program [counter]))
       (AstId 20) [ScalarValue (IntegerValue x)] st []).completion
End

val () = cv_auto_trans static_state_def;
val () = cv_auto_trans run_store_def;

Theorem store_reads_back:
  run_store initial_state 5 = ReturnCompletion [ScalarValue (IntegerValue 5)]
Proof
  CONV_TAC cv_eval
QED

(* The EVM halts exceptionally on SSTORE in a static frame. *)
Theorem static_store_invalid:
  run_store static_state 5 = InvalidCompletion "bad scalar write"
Proof
  CONV_TAC cv_eval
QED

(* Checked identity conversions preserve a calldata slice's offset and length. *)
Theorem calldata_identity_conversion:
  wf_core_value_type test_env (SingleType (LocatedT CalldataLoc BytesT)) ∧
  wf_core_operation test_env
    <| bindings := [(AstId 1, SingleType (LocatedT CalldataLoc BytesT))];
       targets := []; returns := []; in_loop := F |>
    (SingleType (LocatedT CalldataLoc BytesT))
    (ConvertOperation (LocatedT CalldataLoc BytesT) (BoundAtom (AstId 1))) ∧
  eval_pure_operation test_env
    [FEMPTY |+ (1, <| binding_type := SingleType (LocatedT CalldataLoc BytesT);
                      binding_value := ReferenceValue (CalldataReference 7 3 BytesT) |>)]
    (ConvertOperation (LocatedT CalldataLoc BytesT) (BoundAtom (AstId 1))) =
    ValueOk (ReferenceValue (CalldataReference 7 3 BytesT))
Proof
  CONV_TAC cv_eval
QED

(* A memory reference defaults to the zero slot, whatever its type (the
 * elaborated body allocates a static array's zero value before running); a
 * dynamic array there is empty. *)
Theorem memory_reference_defaults:
  eval_operation test_env initial_state
    (DefaultReferenceOperation MemoryLoc (ArrayT u256 (SOME 1))) =
    INL (ReferenceValue (MemoryReference 96 (ArrayT u256 (SOME 1))), initial_state) ∧
  eval_operation test_env initial_state
    (DefaultReferenceOperation MemoryLoc (ArrayT u256 NONE)) =
    INL (ReferenceValue (MemoryReference 96 (ArrayT u256 NONE)), initial_state) ∧
  memory_array_element (ArrayT u256 NONE) 96 0 initial_state =
    INR (PanicCompletion 50)
Proof
  CONV_TAC cv_eval
QED

(* The compiler inspects both length tags before its first storage write. *)
Definition static_byte_copy_def:
  static_byte_copy bad_src bad_dst =
    copy_byte_contents
      (StorageReference PersistentStorage 0w 0w 0 BytesT (LayoutId 1))
      (StorageReference PersistentStorage 0w 1w 0 BytesT (LayoutId 2))
      (static_state with world := static_state.world with accounts :=
        set_storage_word (set_storage_word empty_accounts 0w 0w bad_src) 0w 1w bad_dst)
End

val () = cv_auto_trans static_byte_copy_def;

Theorem invalid_source_header_precedes_static_copy_guard:
  static_byte_copy 64w 0w = INR (PanicCompletion 34)
Proof
  CONV_TAC cv_eval
QED

Theorem invalid_destination_header_precedes_static_copy_guard:
  static_byte_copy 0w 64w = INR (PanicCompletion 34)
Proof
  CONV_TAC cv_eval
QED

Theorem valid_headers_reach_static_copy_guard:
  static_byte_copy 0w 0w = INR (InvalidCompletion "byte copy in static frame")
Proof
  CONV_TAC cv_eval
QED

(* Encoding a corrupt storage argument panics before LOG's static guard. *)
Definition static_byte_event_def:
  static_byte_event header =
    (emit_event test_env NONE [(LocatedT MemoryLoc BytesT, F, BoundAtom (AstId 1))]
      (static_state with <|
        scopes := [FEMPTY |+ (1, <|
          binding_type := SingleType (LocatedT StorageLoc BytesT);
          binding_value := ReferenceValue
            (StorageReference PersistentStorage 0w 0w 0 BytesT (LayoutId 1)) |>)];
        world := static_state.world with accounts :=
          set_storage_word empty_accounts 0w 0w header |>) []).completion
End

val () = cv_auto_trans static_byte_event_def;

Theorem invalid_header_precedes_static_event_guard:
  static_byte_event 64w = PanicCompletion 34
Proof
  CONV_TAC cv_eval
QED

Theorem valid_header_reaches_static_event_guard:
  static_byte_event 0w = InvalidCompletion "emit in static frame"
Proof
  CONV_TAC cv_eval
QED

(* Inline assembly. asm(x) runs code with x bound to the block's "x" and
 * returns x; asm_caller() calls asm(7); halt() stops from a block. *)
Overload ylit = “λn. YulLit (LitNumber n)”

Definition asm_proc_def:
  asm_proc code = <|
    procedure_id := AstId 110;
    parameters := [(AstId 111, u256)];
    return_bindings := [(AstId 112, u256)];
    body := [AssemblyStmt code [("x", AssemblyLocal (AstId 111) u256)];
             ReturnStmt [BoundAtom (AstId 111)]]
  |>
End

Definition asm_caller_def:
  asm_caller = <|
    procedure_id := AstId 120;
    parameters := [];
    return_bindings := [(AstId 121, u256)];
    body := [
      DefineStmt (AstId 122) (SingleType u256)
        (InternalCallOperation (AstId 110) [k 7]);
      ReturnStmt [k 1]]
  |>
End

Definition halt_proc_def:
  halt_proc = <|
    procedure_id := AstId 130;
    parameters := [];
    return_bindings := [];
    body := [AssemblyStmt [YulExprStmt (YulBuiltin YStop [])] []]
  |>
End

Definition asm_env_def:
  asm_env code = core_program_environment <|
    unsupported_procedures := []; procedures := [asm_proc code; asm_caller; halt_proc];
    struct_layouts := []; function_ids := []; type_declarations := [];
    state_variables := []; immutables := [];
    entry_procedure := AstId 110;
    external_functions := []; receive_procedure := NONE;
    fallback_procedure := NONE; creation_procedure := NONE
  |>
End

Definition run_asm_def:
  run_asm code st f args =
    (invoke_source 20 (asm_env code) f args st []).completion
End

Definition store_x_def:
  store_x = YulExprStmt (YulBuiltin YSStore [ylit 0w; YulName "x"])
End

Definition run_halt_def:
  run_halt kind =
    run_entry 20 (asm_env []) halt_proc [] initial_state.frame
      initial_state.world (SOME FEMPTY) 0 NONE kind
End

val () = cv_auto_trans asm_env_def;
val () = cv_auto_trans run_asm_def;
val () = cv_auto_trans store_x_def;
val () = cv_auto_trans run_halt_def;

Theorem asm_writes_local_back:
  run_asm [YulAssign ["x"] (YulBuiltin YAdd [YulName "x"; ylit 1w])]
    initial_state (AstId 110) [ScalarValue (IntegerValue 7)] =
  ReturnCompletion [ScalarValue (IntegerValue 8)]
Proof
  CONV_TAC cv_eval
QED

(* A static frame rejects a block naming sstore, even on a path not taken. *)
Theorem asm_static_store_invalid:
  run_asm [store_x] static_state (AstId 110) [ScalarValue (IntegerValue 7)] =
    InvalidCompletion "unsupported assembly builtin" ∧
  run_asm [YulIf (ylit 0w) [store_x]] static_state (AstId 110)
    [ScalarValue (IntegerValue 7)] =
    InvalidCompletion "unsupported assembly builtin"
Proof
  CONV_TAC cv_eval
QED

(* A block reads back what it wrote anywhere in memory: the scratch space,
 * the zero slot, or from the free memory pointer (0x80 here) up. *)
Theorem asm_memory_round_trips:
  run_asm [YulExprStmt (YulBuiltin YMStore [ylit 0x20w; YulName "x"]);
           YulAssign ["x"] (YulBuiltin YMLoad [ylit 0x20w])]
    initial_state (AstId 110) [ScalarValue (IntegerValue 7)] =
    ReturnCompletion [ScalarValue (IntegerValue 7)] ∧
  run_asm [YulExprStmt (YulBuiltin YMStore [ylit 0x60w; YulName "x"]);
           YulAssign ["x"] (YulBuiltin YAdd [YulBuiltin YMLoad [ylit 0x60w]; ylit 1w])]
    initial_state (AstId 110) [ScalarValue (IntegerValue 7)] =
    ReturnCompletion [ScalarValue (IntegerValue 8)] ∧
  run_asm [YulExprStmt (YulBuiltin YMStore8 [ylit 0x7fw; YulName "x"]);
           YulAssign ["x"] (YulBuiltin YMLoad [ylit 0x60w])]
    initial_state (AstId 110) [ScalarValue (IntegerValue 7)] =
    ReturnCompletion [ScalarValue (IntegerValue 7)] ∧
  run_asm [YulExprStmt (YulBuiltin YMStore [ylit 0x80w; YulName "x"]);
           YulAssign ["x"] (YulBuiltin YAdd [YulBuiltin YMLoad [ylit 0x80w]; ylit 1w])]
    initial_state (AstId 110) [ScalarValue (IntegerValue 7)] =
    ReturnCompletion [ScalarValue (IntegerValue 8)]
Proof
  CONV_TAC cv_eval
QED

(* codesize and codecopy read the code at the frame's code address: a
 * library frame reached by DELEGATECALL runs the library's code for the
 * caller's account. extcodecopy reads any account's code, zero past its end.
 * A creation frame's account has no code yet (the EVM would read the
 * initcode), so a block naming either fails closed there, even on a path
 * not taken. *)
Definition code_state_def:
  code_state = initial_state with <|
    frame := initial_state.frame with
      <| self_address := 0x10w; code_address := 0x20w |>;
    world := initial_state.world with accounts :=
      update_account 0x20w (empty_account_state with code := [1w; 2w; 3w])
        (update_account 0x10w (empty_account_state with code := [9w])
           empty_accounts) |>
End

Definition load_x_def:
  load_x = YulAssign ["x"] (YulBuiltin YMLoad [ylit 0w])
End

val () = List.app cv_auto_trans [code_state_def, load_x_def];

Theorem asm_code_reads_code_address:
  run_asm [YulAssign ["x"] (YulBuiltin YCodeSize [])] code_state (AstId 110)
    [ScalarValue (IntegerValue 7)] =
    ReturnCompletion [ScalarValue (IntegerValue 3)] ∧
  run_asm [YulExprStmt (YulBuiltin YCodeCopy [ylit 0w; ylit 1w; ylit 32w]);
           load_x] code_state (AstId 110) [ScalarValue (IntegerValue 7)] =
    ReturnCompletion [ScalarValue (IntegerValue (&(0x203 * 2 ** 240)))] ∧
  run_asm [YulExprStmt (YulBuiltin YExtCodeCopy
             [ylit 0x10w; ylit 0w; ylit 0w; ylit 32w]); load_x]
    code_state (AstId 110) [ScalarValue (IntegerValue 7)] =
    ReturnCompletion [ScalarValue (IntegerValue (&(9 * 2 ** 248)))]
Proof
  CONV_TAC cv_eval
QED

Theorem asm_code_in_creation_frame_invalid:
  run_asm [YulAssign ["x"] (YulBuiltin YCodeSize [])] initial_state (AstId 110)
    [ScalarValue (IntegerValue 7)] =
    InvalidCompletion "unsupported assembly builtin" ∧
  run_asm [YulIf (ylit 0w)
             [YulExprStmt (YulBuiltin YCodeCopy [ylit 0w; ylit 0w; ylit 32w])]]
    initial_state (AstId 110) [ScalarValue (IntegerValue 7)] =
    InvalidCompletion "unsupported assembly builtin"
Proof
  CONV_TAC cv_eval
QED

(* blockhash reads one of the 256 blocks before the current one, most recent
 * first, as verifereum's step_block_hash does, and 0 past the hashes given. *)
Definition hash_tx_def:
  hash_tx = initial_state.frame.tx_params with
    <| blockNumber := 300; prevHashes := GENLIST (λi. n2w (i + 1)) 256 |>
End

Theorem block_hash_word_window:
  block_hash_word hash_tx 299 = 1w ∧
  block_hash_word hash_tx 44 = 256w ∧
  block_hash_word hash_tx 43 = 0w ∧
  block_hash_word hash_tx 300 = 0w ∧
  block_hash_word hash_tx 301 = 0w ∧
  block_hash_word (hash_tx with prevHashes := [5w]) 299 = 5w ∧
  block_hash_word (hash_tx with prevHashes := [5w]) 298 = 0w
Proof
  EVAL_TAC
QED

(* Memory byte sequences. asm_blocks runs blocks one after another with b's
 * address bound to each block's "b" and returns its "r"; run_asm_blocks gives
 * the completion and b's bytes afterwards, and run_asm_bytes runs one block.
 * b is the first allocation, at 0x80: its length word, then its bytes, then
 * the zero word the copy's cleanup writes; the free memory pointer is 0xc0. *)
Definition asm_blocks_def:
  (asm_blocks [] = [ReturnStmt [BoundAtom (AstId 142)]]) ∧
  (asm_blocks (code :: codes) =
    AssemblyStmt code [("b", AssemblyMemory (AstId 141) BytesT);
                       ("r", AssemblyLocal (AstId 142) u256)] ::
    asm_blocks codes)
End

Definition asm_bytes_proc_def:
  asm_bytes_proc codes = <|
    procedure_id := AstId 140;
    parameters := [(AstId 141, LocatedT MemoryLoc BytesT)];
    return_bindings := [(AstId 142, u256)];
    body := asm_blocks codes
  |>
End

Definition run_asm_blocks_def:
  run_asm_blocks codes bs =
    case new_byte_array bs initial_state of
      INR c => (c, [])
    | INL (b, st) =>
        let env = core_program_environment <|
          unsupported_procedures := []; procedures := [asm_bytes_proc codes];
          struct_layouts := []; function_ids := []; type_declarations := [];
          state_variables := []; immutables := [];
          entry_procedure := AstId 140;
          external_functions := []; receive_procedure := NONE;
          fallback_procedure := NONE; creation_procedure := NONE |> in
        let r = invoke_source 20 env (AstId 140)
                  [ReferenceValue (MemoryReference b BytesT)] st [] in
        (r.completion, FST (memory_bytes b r.state))
End

Definition run_asm_bytes_def:
  run_asm_bytes code bs = run_asm_blocks [code] bs
End

val () = cv_auto_trans run_asm_blocks_def;
val () = cv_auto_trans run_asm_bytes_def;

Overload yadd = “λe1 e2. YulBuiltin YAdd [e1; e2]”

(* The block sees b's address, length word and bytes; a byte or a whole word
 * written in b's data is read back (the bytes past the length are dropped),
 * and a word written to its length word is its new length. *)
Theorem asm_memory_bytes:
  run_asm_bytes [YulAssign ["r"] (YulName "b")] [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue 0x80)], [1w; 2w; 3w]) ∧
  run_asm_bytes [YulAssign ["r"] (YulBuiltin YMLoad [YulName "b"])] [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue 3)], [1w; 2w; 3w]) ∧
  run_asm_bytes [YulAssign ["r"] (YulBuiltin YShr [ylit 232w;
                   YulBuiltin YMLoad [yadd (YulName "b") (ylit 32w)]])] [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue 0x010203)], [1w; 2w; 3w]) ∧
  run_asm_bytes [YulExprStmt (YulBuiltin YMStore8 [yadd (YulName "b") (ylit 33w); ylit 0xffw])]
    [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue 0)], [1w; 0xffw; 3w]) ∧
  run_asm_bytes [YulExprStmt (YulBuiltin YMStore [yadd (YulName "b") (ylit 32w); ylit 0xaabbw])]
    [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue 0)], [0w; 0w; 0w]) ∧
  run_asm_bytes [YulExprStmt (YulBuiltin YMStore [YulName "b"; ylit 1w])] [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue 0)], [1w]) ∧
  run_asm_bytes [YulExprStmt (YulBuiltin YMStore8 [yadd (YulName "b") (ylit 64w); ylit 1w])]
    [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue 0)], [1w; 2w; 3w])
Proof
  CONV_TAC cv_eval
QED

(* A block reads any address, however computed: the free memory pointer,
 * past b's two words; scratch and memory nobody wrote, as zeros; a word
 * straddling b's data and the cleanup word after it. *)
Theorem asm_memory_reads:
  run_asm_bytes [YulLet ["p"] (SOME (ylit 0x40w));
                 YulAssign ["r"] (YulBuiltin YMLoad [YulName "p"])] [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue 0xc0)], [1w; 2w; 3w]) ∧
  run_asm_bytes [YulExprStmt (YulBuiltin YMStore [ylit 0x40w; ylit 0x100w])]
    [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue 0)], [1w; 2w; 3w]) ∧
  run_asm_bytes [YulAssign ["r"] (YulBuiltin YMLoad [yadd (YulName "b") (ylit 0x60w)])]
    [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue 0)], [1w; 2w; 3w]) ∧
  run_asm_bytes [YulLet ["p"] (SOME (ylit 0w));
                 YulAssign ["r"] (YulBuiltin YMLoad [YulName "p"])] [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue 0)], [1w; 2w; 3w]) ∧
  run_asm_bytes [YulLet ["p"] (SOME (ylit 0w));
                 YulExprStmt (YulBuiltin YMStore [YulName "p"; ylit 5w]);
                 YulAssign ["r"] (YulBuiltin YMLoad [YulName "p"])] [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue 5)], [1w; 2w; 3w]) ∧
  run_asm_bytes [YulLet ["p"] (SOME (ylit 0x60w));
                 YulAssign ["r"] (YulBuiltin YMLoad [YulName "p"])] [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue 0)], [1w; 2w; 3w]) ∧
  run_asm_bytes [YulAssign ["r"] (YulBuiltin YMLoad [yadd (YulName "b") (ylit 0x21w)])]
    [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue (0x0203 * 2 ** 240))], [1w; 2w; 3w])
Proof
  CONV_TAC cv_eval
QED

(* Memory arrays of value types. run_asm_array ty vs code runs code on an
 * array of type ty holding vs, the first allocation (at 0x80), with its
 * address bound to "a", and gives the block's "r" and the elements after. *)
Definition asm_array_proc_def:
  asm_array_proc ty code = <|
    procedure_id := AstId 140;
    parameters := [(AstId 141, LocatedT MemoryLoc ty)];
    return_bindings := [(AstId 142, u256)];
    body := [AssemblyStmt code [("a", AssemblyMemory (AstId 141) ty);
                                ("r", AssemblyLocal (AstId 142) u256)];
             ReturnStmt [BoundAtom (AstId 142)]]
  |>
End

Definition asm_array_env_def:
  asm_array_env ty code = core_program_environment <|
    unsupported_procedures := []; procedures := [asm_array_proc ty code];
    struct_layouts := []; function_ids := []; type_declarations := [];
    state_variables := []; immutables := [];
    entry_procedure := AstId 140;
    external_functions := []; receive_procedure := NONE;
    fallback_procedure := NONE; creation_procedure := NONE |>
End

(* The words of the scalars vs, from p up. *)
Definition store_words_def:
  (store_words env ty p [] st = st) ∧
  (store_words env ty p (v :: vs) st =
    store_words env ty (p + 32) vs
      (case write_memory_word env ty p (ScalarValue v) st of
         INL st1 => st1
       | INR _ => st))
End

Definition run_asm_array_def:
  run_asm_array ty vs code =
    case ty of
      ArrayT element length =>
        let n = LENGTH vs in
        let env = asm_array_env ty code in
        let data = if length = NONE then 0xa0 else 0x80 in
        let st = store_words env element data vs
                   (memory_store 64 (data + 32 * n)
                      (if length = NONE then memory_store 0x80 n initial_state
                       else initial_state)) in
        let r = invoke_source 20 env (AstId 140)
                  [ReferenceValue (MemoryReference 0x80 ty)] st [] in
        (r.completion,
         case memory_value env F 0 ty (ReferenceValue (MemoryReference 0x80 ty)) r.state of
           INL (TupleValue us, _) => us
         | _ => [])
    | _ => (InvalidCompletion "not an array", [])
End

(* The same block run on an empty dynamic array, the zero slot. *)
Definition run_asm_null_def:
  run_asm_null ty code =
    (invoke_source 20 (asm_array_env ty code) (AstId 140)
       [ReferenceValue (MemoryReference 96 ty)] initial_state []).completion
End

val () = cv_auto_trans store_words_def;
val () = cv_auto_trans run_asm_array_def;
val () = cv_auto_trans run_asm_null_def;

Definition uints_def:
  uints ns = MAP (λn. IntegerValue (&n)) ns
End

Definition scalars_def:
  scalars vs = MAP ScalarValue vs
End

val () = cv_auto_trans uints_def;
val () = cv_auto_trans scalars_def;

(* A dynamic array has its length word at its address and a word per element
 * after it; a static one has no length word. A word written in an element
 * reads back as the compiler's cleanup leaves it: a uint8's low byte, a bool
 * nonzero, an address's low 160 bits. A word written to the length word is
 * the new length. A negative element is sign-extended. An empty dynamic array
 * is the zero slot, 0x60. *)
Theorem asm_memory_arrays:
  run_asm_array (ArrayT (UintT 8) NONE) (uints [1; 2; 3])
    [YulAssign ["r"] (YulBuiltin YMLoad [YulName "a"])] =
    (ReturnCompletion [ScalarValue (IntegerValue 3)],
     scalars (uints [1; 2; 3])) ∧
  run_asm_array (ArrayT (UintT 8) NONE) (uints [1; 2; 3])
    [YulAssign ["r"] (YulBuiltin YMLoad [yadd (YulName "a") (ylit 0x40w)])] =
    (ReturnCompletion [ScalarValue (IntegerValue 2)],
     scalars (uints [1; 2; 3])) ∧
  run_asm_array (ArrayT (UintT 8) NONE) (uints [1; 2; 3])
    [YulExprStmt (YulBuiltin YMStore [yadd (YulName "a") (ylit 0x60w); ylit 9w])] =
    (ReturnCompletion [ScalarValue (IntegerValue 0)],
     scalars (uints [1; 2; 9])) ∧
  run_asm_array (ArrayT (UintT 8) NONE) (uints [1; 2; 3])
    [YulExprStmt (YulBuiltin YMStore [yadd (YulName "a") (ylit 0x20w); ylit 0x105w])] =
    (ReturnCompletion [ScalarValue (IntegerValue 0)],
     scalars (uints [5; 2; 3])) ∧
  run_asm_array (ArrayT (UintT 8) NONE) (uints [1; 2; 3])
    [YulExprStmt (YulBuiltin YMStore [YulName "a"; ylit 2w])] =
    (ReturnCompletion [ScalarValue (IntegerValue 0)],
     scalars (uints [1; 2])) ∧
  run_asm_array (ArrayT BoolT NONE) [BoolValue F]
    [YulExprStmt (YulBuiltin YMStore [yadd (YulName "a") (ylit 0x20w); ylit 2w])] =
    (ReturnCompletion [ScalarValue (IntegerValue 0)], [ScalarValue (BoolValue T)]) ∧
  run_asm_array (ArrayT (AddressT NonpayableAddress) NONE) [AddressValue 0w]
    [YulExprStmt (YulBuiltin YMStore [yadd (YulName "a") (ylit 0x20w);
       YulBuiltin YShl [ylit 160w; ylit 1w]])] =
    (ReturnCompletion [ScalarValue (IntegerValue 0)], [ScalarValue (AddressValue 0w)]) ∧
  run_asm_array (ArrayT (IntT 8) NONE) [IntegerValue (-1)]
    [YulAssign ["r"] (YulBuiltin YMLoad [yadd (YulName "a") (ylit 0x20w)])] =
    (ReturnCompletion [ScalarValue (IntegerValue 115792089237316195423570985008687907853269984665640564039457584007913129639935)],
     [ScalarValue (IntegerValue (-1))]) ∧
  run_asm_array (ArrayT (UintT 256) (SOME 2)) (uints [5; 6])
    [YulAssign ["r"] (YulBuiltin YMLoad [YulName "a"]);
     YulExprStmt (YulBuiltin YMStore [yadd (YulName "a") (ylit 0x20w); ylit 7w])] =
    (ReturnCompletion [ScalarValue (IntegerValue 5)],
     scalars (uints [5; 7])) ∧
  run_asm_null (ArrayT (UintT 256) NONE) [YulAssign ["r"] (YulName "a")] =
    ReturnCompletion [ScalarValue (IntegerValue 0x60)]
Proof
  CONV_TAC cv_eval
QED

(* Memory from the free memory pointer (0xc0 here) up is not reclaimed after
 * a block: the next block reads what the last wrote there. *)
Theorem asm_memory_temporary:
  run_asm_bytes [YulExprStmt (YulBuiltin YMStore [yadd (YulName "b") (ylit 0x40w); ylit 5w]);
                 YulAssign ["r"] (YulBuiltin YMLoad [yadd (YulName "b") (ylit 0x40w)])]
    [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue 5)], [1w; 2w; 3w]) ∧
  run_asm_blocks
    [[YulExprStmt (YulBuiltin YMStore [ylit 0xc0w; ylit 5w])];
     [YulAssign ["r"] (YulBuiltin YMLoad [ylit 0xc0w])]] [1w; 2w; 3w] =
    (ReturnCompletion [ScalarValue (IntegerValue 5)], [1w; 2w; 3w])
Proof
  CONV_TAC cv_eval
QED

(* Allocation. run_asm_alloc ty1 ty2 code runs code with memory locals "a"
 * of type ty1 and "b" of type ty2, both at first the zero slot (0x60), and
 * "c", a uint256[] holding [5] at 0x80, so the free memory pointer starts at
 * 0xc0; it returns a and b. It gives the completion, each returned
 * reference's address and the value there, and the free memory pointer
 * after. *)
Definition asm_alloc_proc_def:
  asm_alloc_proc ty1 ty2 code = <|
    procedure_id := AstId 140;
    parameters := [(AstId 143, LocatedT MemoryLoc (ArrayT (UintT 256) NONE))];
    return_bindings := [(AstId 141, LocatedT MemoryLoc ty1);
                        (AstId 142, LocatedT MemoryLoc ty2)];
    body := [AssemblyStmt code [("a", AssemblyMemory (AstId 141) ty1);
                                ("b", AssemblyMemory (AstId 142) ty2);
                                ("c", AssemblyMemory (AstId 143) (ArrayT (UintT 256) NONE))];
             ReturnStmt [BoundAtom (AstId 141); BoundAtom (AstId 142)]]
  |>
End

Definition asm_alloc_object_def:
  asm_alloc_object env (st : source_state) v =
    case v of
      ReferenceValue (MemoryReference p ty) =>
        (case memory_value env F 0 ty v st of
           INL (u, _) => SOME (p, u)
         | INR _ => NONE)
    | _ => NONE
End

Definition run_asm_alloc_def:
  run_asm_alloc ty1 ty2 code =
    let c = ArrayT (UintT 256) NONE in
    let st = memory_store 64 0xc0 (memory_store 0xa0 5 (memory_store 0x80 1 initial_state)) in
    let env = core_program_environment <|
      unsupported_procedures := []; procedures := [asm_alloc_proc ty1 ty2 code];
      struct_layouts := []; function_ids := []; type_declarations := [];
      state_variables := []; immutables := [];
      entry_procedure := AstId 140;
      external_functions := []; receive_procedure := NONE;
      fallback_procedure := NONE; creation_procedure := NONE |> in
    let r = invoke_source 20 env (AstId 140)
              [ReferenceValue (MemoryReference 0x80 c)] st [] in
    (r.completion,
     (case r.completion of
        ReturnCompletion vs => MAP (asm_alloc_object env r.state) vs
      | _ => []),
     FST (memory_load 64 r.state))
End

val () = cv_auto_trans asm_alloc_object_def;
val () = cv_auto_trans run_asm_alloc_def;

Overload ymstore = “λp v. YulExprStmt (YulBuiltin YMStore [p; v])”
Overload yname = “YulName”
Overload uarr = “ArrayT (UintT 256) NONE”

(* OpenZeppelin's _asSingletonArrays: two one-element arrays from the free
 * memory pointer, which then points past them. *)
Definition singletons_def:
  singletons top =
    [YulAssign ["a"] (YulBuiltin YMLoad [ylit 0x40w]);
     ymstore (yname "a") (ylit 1w);
     ymstore (yadd (yname "a") (ylit 0x20w)) (ylit 7w);
     YulAssign ["b"] (yadd (yname "a") (ylit 0x40w));
     ymstore (yname "b") (ylit 1w);
     ymstore (yadd (yname "b") (ylit 0x20w)) (ylit 9w);
     ymstore (ylit 0x40w) (yadd (yname "b") top)]
End

(* Uniswap v4's callHook, with three bytes written as the return data copy
 * would, its padding left unwritten. *)
Definition hook_bytes_def:
  hook_bytes =
    [YulAssign ["a"] (YulBuiltin YMLoad [ylit 0x40w]);
     ymstore (ylit 0x40w) (yadd (yname "a") (ylit 0x40w));
     ymstore (yname "a") (ylit 3w);
     YulExprStmt (YulBuiltin YMStore8 [yadd (yname "a") (ylit 0x20w); ylit 1w]);
     YulExprStmt (YulBuiltin YMStore8 [yadd (yname "a") (ylit 0x21w); ylit 2w]);
     YulExprStmt (YulBuiltin YMStore8 [yadd (yname "a") (ylit 0x22w); ylit 3w])]
End

val () = cv_auto_trans singletons_def;
val () = cv_auto_trans hook_bytes_def;

Definition u256s_def:
  u256s ns = MAP (λn. ScalarValue (IntegerValue (&n))) ns
End

val () = cv_auto_trans u256s_def;

Definition mref_def:
  mref p ty = ReferenceValue (MemoryReference p ty)
End

val () = cv_auto_trans mref_def;

(* A block allocates by writing objects from the free memory pointer and
 * raising it past them; a memory local is rebound to the address the block
 * leaves in it, and the source reads the object there. *)
Theorem asm_memory_alloc:
  run_asm_alloc uarr uarr (singletons (ylit 0x40w)) =
    (ReturnCompletion [mref 0xc0 uarr; mref 0x100 uarr],
     [SOME (0xc0, TupleValue (u256s [7])); SOME (0x100, TupleValue (u256s [9]))],
     0x140) ∧
  run_asm_alloc BytesT uarr hook_bytes =
    (ReturnCompletion [mref 0xc0 BytesT; mref 0x60 uarr],
     [SOME (0xc0, ScalarValue (BytesValue [1w; 2w; 3w])); SOME (0x60, TupleValue [])],
     0x100) ∧
  (* the pointer raised with nothing left there *)
  run_asm_alloc uarr uarr [ymstore (ylit 0x40w) (ylit 0x200w)] =
    (ReturnCompletion [mref 0x60 uarr; mref 0x60 uarr],
     [SOME (0x60, TupleValue []); SOME (0x60, TupleValue [])], 0x200) ∧
  (* two locals at one object *)
  run_asm_alloc uarr uarr
    [YulAssign ["a"] (YulBuiltin YMLoad [ylit 0x40w]);
     YulAssign ["b"] (yname "a");
     ymstore (yname "a") (ylit 0w);
     ymstore (ylit 0x40w) (yadd (yname "a") (ylit 0x20w))] =
    (ReturnCompletion [mref 0xc0 uarr; mref 0xc0 uarr],
     [SOME (0xc0, TupleValue []); SOME (0xc0, TupleValue [])], 0xe0)
Proof
  CONV_TAC cv_eval
QED

(* A literal after a block that raised the free memory pointer is allocated
 * past it, and panics as the compiler's allocator does when it would pass
 * 2^64. *)
Definition run_asm_literal_def:
  run_asm_literal code =
    let proc = <|
      procedure_id := AstId 160; parameters := [];
      return_bindings := [(AstId 161, LocatedT MemoryLoc BytesT)];
      body := [AssemblyStmt code [];
               DefineStmt (AstId 162) (SingleType (LocatedT MemoryLoc BytesT))
                 (BytesLiteralOperation BytesT [0x78w]);
               ReturnStmt [BoundAtom (AstId 162)]] |> in
    let env = core_program_environment <|
      unsupported_procedures := []; procedures := [proc];
      struct_layouts := []; function_ids := []; type_declarations := [];
      state_variables := []; immutables := [];
      entry_procedure := AstId 160;
      external_functions := []; receive_procedure := NONE;
      fallback_procedure := NONE; creation_procedure := NONE |> in
    let r = invoke_source 20 env (AstId 160) [] initial_state [] in
    (r.completion,
     (case r.completion of
        ReturnCompletion vs => MAP (asm_alloc_object env r.state) vs
      | _ => []))
End

val () = cv_auto_trans run_asm_literal_def;

Theorem asm_memory_alloc_literal:
  run_asm_literal [ymstore (ylit 0x40w) (ylit 0x100w)] =
    (ReturnCompletion [mref 0x100 BytesT],
     [SOME (0x100, ScalarValue (BytesValue [0x78w]))]) ∧
  FST (run_asm_literal [ymstore (ylit 0x40w) (ylit 0xFFFFFFFFFFFFFFE0w)]) =
    PanicCompletion 65
Proof
  CONV_TAC cv_eval
QED

(* A storage byte sequence of length 2^64 or more is not encoded in place:
 * the memory for its encoding cannot be allocated, so it panics with 0x41, as
 * a read of its contents does. *)
Definition long_bytes_accounts_def:
  long_bytes_accounts =
    update_account 0w (empty_account_state with
      storage := update_storage 0w (n2w (2 * 2 ** 64 + 1)) empty_storage)
      empty_accounts
End

Theorem storage_abi_value_bytes_too_long:
  storage_abi_value env 0 long_bytes_accounts 0w 0w BytesT = INR (PanicCompletion 65) ∧
  storage_byte_contents long_bytes_accounts
    (StorageReference PersistentStorage 0w 0w 0 BytesT (LayoutId 0)) =
  INR (PanicCompletion 65)
Proof
  simp[Once solidityABITheory.storage_abi_value_def, long_bytes_accounts_def] >> EVAL_TAC
QED

(* return(...) in a callee ends the whole frame with its bytes. *)
Theorem asm_halt_passes_through_call:
  run_asm [YulExprStmt (YulBuiltin YMStore [ylit 0w; YulName "x"]);
           YulExprStmt (YulBuiltin YReturn [ylit 0w; ylit 32w])]
    initial_state (AstId 120) [] =
  HaltCompletion (REPLICATE 31 0w ++ [7w])
Proof
  CONV_TAC cv_eval
QED

(* A halt returns its bytes from a call frame and fails closed in a creation
 * frame. *)
Theorem asm_halt_in_creation_invalid:
  run_halt CallEntry = ContractReturned [] initial_state.world ∧
  run_halt CreationEntry = ContractInvalid "assembly halt in a creation frame"
Proof
  CONV_TAC cv_eval
QED

(* call(gas(), a, 0, i, isz, o, osz) with literal arguments. *)
Definition ycall_def:
  ycall a i isz out osz =
    YulBuiltin YCall [YulBuiltin YGas []; a; ylit 0w; ylit i; ylit isz;
                      ylit out; ylit osz]
End

(* What assembly_calls_ok admits: gas() only as a call's gas argument, and
 * return data only after a statement that calls, earlier in the same or an
 * enclosing statement list. *)
Theorem asm_calls_rule:
  assembly_calls_ok
    [YulLet ["s"] (SOME (ycall (YulName "t") 0w 0w 0w 32w));
     YulIf (YulBuiltin YIsZero [YulName "s"])
       [YulExprStmt (YulBuiltin YReturnDataCopy
          [ylit 0w; ylit 0w; YulBuiltin YReturnDataSize []])];
     YulAssign ["x"] (YulBuiltin YReturnDataSize [])] ∧
  assembly_calls_ok
    [YulLet ["s"] (SOME (YulBuiltin YStaticCall
       [ylit 5000w; YulName "t"; ylit 0w; ylit 0w; ylit 0w; ylit 0w]));
     YulAssign ["x"] (YulBuiltin YReturnDataSize [])] ∧
  assembly_calls_ok
    [YulIf (YulBuiltin YIsZero [ycall (YulName "t") 0w 0w 0w 0w])
       [YulExprStmt (YulBuiltin YRevert [ylit 0w; YulBuiltin YReturnDataSize []])]] ∧
  ¬assembly_calls_ok
    [YulIf (YulBuiltin YIsZero [ycall (YulName "t") 0w 0w 0w 0w]) [];
     YulAssign ["x"] (YulBuiltin YReturnDataSize [])] ∧
  ¬assembly_calls_ok [YulAssign ["x"] (YulBuiltin YReturnDataSize [])] ∧
  assembly_calls_ok [YulAssign ["x"] (YulBuiltin YGas [])] ∧
  assembly_calls_ok
    [YulLet ["s"] (SOME (YulBuiltin YCall
       [ylit 0w; YulBuiltin YGas []; ylit 0w; ylit 0w; ylit 0w; ylit 0w; ylit 0w]))] ∧
  ¬assembly_calls_ok
    [YulAssign ["x"] (yadd (ycall (YulName "t") 0w 0w 0w 0w)
                            (YulBuiltin YReturnDataSize []))] ∧
  ¬assembly_calls_ok
    [YulIf (YulName "x") [YulLet ["s"] (SOME (ycall (YulName "t") 0w 0w 0w 0w))];
     YulAssign ["x"] (YulBuiltin YReturnDataSize [])] ∧
  ¬assembly_calls_ok
    [YulLet ["s"] (SOME (ycall (YulName "t") 0w 0w 0w 0w));
     YulFunction "f" [] ["r"] [YulAssign ["r"] (YulBuiltin YReturnDataSize [])]]
Proof
  EVAL_TAC
QED

(* Arguments run right to left: a call's return data covers a read in an
 * argument left of it, but not to its right. *)
Theorem asm_argument_order_rule:
  assembly_calls_ok
    [YulAssign ["x"] (YulBuiltin YAnd
       [YulBuiltin YGt [YulBuiltin YReturnDataSize []; ylit 31w];
        ycall (YulName "t") 0w 0w 0w 32w])] ∧
  ¬assembly_calls_ok
    [YulAssign ["x"] (YulBuiltin YAnd
       [ycall (YulName "t") 0w 0w 0w 32w;
        YulBuiltin YGt [YulBuiltin YReturnDataSize []; ylit 31w]])]
Proof
  EVAL_TAC
QED

(* A Yul function's body may read return data where the block may at its
 * start: always when the source knows the return data (assembly_gas_ok),
 * and otherwise only after a call of the body's own, since the function may
 * be called before any of the block's calls. *)
Theorem asm_function_return_data_rule:
  assembly_gas_ok
    [YulFunction "f" [] ["r"] [YulAssign ["r"] (YulBuiltin YReturnDataSize [])]] ∧
  ¬assembly_calls_ok
    [YulFunction "f" [] ["r"] [YulAssign ["r"] (YulBuiltin YReturnDataSize [])]] ∧
  ¬assembly_calls_ok
    [YulLet ["x"] (SOME (YulApply "f" []));
     YulLet ["s"] (SOME (ycall (YulName "t") 0w 0w 0w 0w));
     YulFunction "f" [] ["r"] [YulAssign ["r"] (YulBuiltin YReturnDataSize [])]] ∧
  assembly_calls_ok
    [YulFunction "f" [] ["r"]
       [YulLet ["s"] (SOME (ycall (YulName "t") 0w 0w 0w 0w));
        YulAssign ["r"] (YulBuiltin YReturnDataSize [])]]
Proof
  EVAL_TAC
QED

(* Enum and user-defined value type locals. asm_typed ty code v runs code on
 * a local of type ty holding v, bound to the block's "x", and returns it. The
 * enum 900 has three members; the user-defined value type 901 is a bytes4,
 * kept left-aligned like one. *)
Definition asm_typed_def:
  asm_typed ty code v =
    let p = <| procedure_id := AstId 110;
               parameters := [(AstId 111, ty)];
               return_bindings := [(AstId 112, ty)];
               body := [AssemblyStmt code [("x", AssemblyLocal (AstId 111) ty)];
                        ReturnStmt [BoundAtom (AstId 111)]] |> in
    let env = core_program_environment <|
      unsupported_procedures := []; procedures := [p];
      struct_layouts := [];
      function_ids := []; type_declarations := [(AstId 900, EnumDeclaration 3);
                            (AstId 901, UserValueDeclaration (FixedBytesT 4))];
      state_variables := []; immutables := [];
      entry_procedure := AstId 110;
      external_functions := []; receive_procedure := NONE;
      fallback_procedure := NONE; creation_procedure := NONE |> in
    (invoke_source 20 env (AstId 110) [ScalarValue v] initial_state []).completion
End

val () = cv_auto_trans asm_typed_def;

(* An enum word reads as its member's index; a word written back past the
 * last member fails closed. A user-defined value type's word is its
 * underlying type's, and a non-canonical one fails closed. *)
Theorem asm_enum_udvt_locals:
  asm_typed (EnumT (AstId 900)) [YulAssign ["x"] (yadd (YulName "x") (ylit 1w))]
    (IntegerValue 1) =
    ReturnCompletion [ScalarValue (IntegerValue 2)] ∧
  asm_typed (EnumT (AstId 900)) [YulAssign ["x"] (ylit 3w)] (IntegerValue 1) =
    InvalidCompletion "assembly write-back failed" ∧
  asm_typed (UserValueT (AstId 901))
    [YulAssign ["x"] (YulBuiltin YShr [ylit 224w; YulName "x"])]
    (BytesValue [0w; 0w; 0w; 7w]) =
    InvalidCompletion "assembly write-back failed" ∧
  asm_typed (UserValueT (AstId 901))
    [YulAssign ["x"] (YulBuiltin YShl [ylit 8w; YulName "x"])]
    (BytesValue [1w; 2w; 3w; 4w]) =
    ReturnCompletion [ScalarValue (BytesValue [2w; 3w; 4w; 0w])]
Proof
  CONV_TAC cv_eval
QED

(* Callees at 0x5000 (returns the word 0x2a), 0x5001 (reverts with the word
 * 0xaa) and 0x5002 (no code). *)
Definition call_state_def:
  call_state =
    initial_state with world := (initial_state.world with accounts :=
      update_account 0x5001w
        (empty_account_state with
           code := [0x60w; 0xaaw; 0x60w; 0w; 0x52w; 0x60w; 0x20w; 0x60w; 0w; 0xfdw])
        (update_account 0x5000w
           (empty_account_state with
              code := [0x60w; 0x2aw; 0x60w; 0w; 0x52w; 0x60w; 0x20w; 0x60w; 0w; 0xf3w])
           empty_accounts))
End

val () = cv_auto_trans ycall_def;
val () = cv_auto_trans call_state_def;

(* A call runs the callee and leaves its output and return data; a failed one
 * is bubbled through the free memory pointer, as SafeERC20 does; a callee
 * returning less than asked leaves the scratch as it was. A static frame
 * refuses call but runs staticcall. *)
Theorem asm_calls_run:
  run_asm [YulExprStmt (YulBuiltin YPop [ycall (ylit 0x5000w) 0w 0w 0w 32w]);
           YulAssign ["x"] (yadd (YulBuiltin YMLoad [ylit 0w])
                                 (YulBuiltin YReturnDataSize []))]
    call_state (AstId 110) [ScalarValue (IntegerValue 7)] =
    ReturnCompletion [ScalarValue (IntegerValue 74)] ∧
  run_asm [YulIf (YulBuiltin YIsZero [ycall (ylit 0x5001w) 0w 0w 0w 0w])
             [YulLet ["p"] (SOME (YulBuiltin YMLoad [ylit 0x40w]));
              YulExprStmt (YulBuiltin YReturnDataCopy
                [YulName "p"; ylit 0w; YulBuiltin YReturnDataSize []]);
              YulExprStmt (YulBuiltin YRevert
                [YulName "p"; YulBuiltin YReturnDataSize []])]]
    call_state (AstId 110) [ScalarValue (IntegerValue 7)] =
    RevertCompletion (REPLICATE 31 0w ++ [0xaaw]) ∧
  run_asm [YulExprStmt (YulBuiltin YPop [ycall (ylit 0x5002w) 0w 0w 0w 32w]);
           YulAssign ["x"] (YulBuiltin YMLoad [ylit 0w])]
    call_state (AstId 110) [ScalarValue (IntegerValue 7)] =
    ReturnCompletion [ScalarValue (IntegerValue 0)] ∧
  run_asm [YulAssign ["x"] (ycall (ylit 0x5000w) 0w 0w 0w 32w)]
    (call_state with frame := call_state.frame with static_context := T)
    (AstId 110) [ScalarValue (IntegerValue 7)] =
    InvalidCompletion "unsupported assembly builtin" ∧
  run_asm [YulAssign ["x"] (YulBuiltin YStaticCall
             [YulBuiltin YGas []; ylit 0x5000w; ylit 0w; ylit 0w; ylit 0w; ylit 32w])]
    (call_state with frame := call_state.frame with static_context := T)
    (AstId 110) [ScalarValue (IntegerValue 7)] =
    ReturnCompletion [ScalarValue (IntegerValue 1)]
Proof
  CONV_TAC cv_eval
QED

(* A callee at 0x5005 returning ADDRESS, and a delegatecall to it. *)
Definition delegate_state_def:
  delegate_state =
    call_state with world := (call_state.world with accounts :=
      update_account 0x5005w
        (empty_account_state with
           code := [0x30w; 0x60w; 0w; 0x52w; 0x60w; 0x20w; 0x60w; 0w; 0xf3w])
        call_state.world.accounts)
End

Definition ydelegate_def:
  ydelegate a out osz =
    YulBuiltin YDelegateCall [YulBuiltin YGas []; a; ylit 0w; ylit 0w;
                              ylit out; ylit osz]
End

val () = cv_auto_trans delegate_state_def;
val () = cv_auto_trans ydelegate_def;

(* A delegatecall is a call to the static rules: gas() as its gas argument,
 * and return data after it. It runs the callee's code as this account (0
 * here), where a call runs it as the callee; a static frame refuses it. *)
Theorem asm_delegate_call:
  assembly_calls_ok
    [YulLet ["s"] (SOME (ydelegate (YulName "t") 0w 32w));
     YulAssign ["x"] (YulBuiltin YReturnDataSize [])] ∧
  run_asm [YulExprStmt (YulBuiltin YPop [ydelegate (ylit 0x5005w) 0w 32w]);
           YulAssign ["x"] (yadd (YulBuiltin YMLoad [ylit 0w])
                                 (YulBuiltin YReturnDataSize []))]
    delegate_state (AstId 110) [ScalarValue (IntegerValue 7)] =
    ReturnCompletion [ScalarValue (IntegerValue 32)] ∧
  run_asm [YulExprStmt (YulBuiltin YPop [ycall (ylit 0x5005w) 0w 0w 0w 32w]);
           YulAssign ["x"] (yadd (YulBuiltin YMLoad [ylit 0w])
                                 (YulBuiltin YReturnDataSize []))]
    delegate_state (AstId 110) [ScalarValue (IntegerValue 7)] =
    ReturnCompletion [ScalarValue (IntegerValue 0x5025)] ∧
  run_asm [YulAssign ["x"] (ydelegate (ylit 0x5005w) 0w 32w)]
    (delegate_state with frame := delegate_state.frame with static_context := T)
    (AstId 110) [ScalarValue (IntegerValue 7)] =
    InvalidCompletion "unsupported assembly builtin"
Proof
  CONV_TAC cv_eval
QED

(* Callees at 0x5003 (returns the bytes 01 02 03) and 0x5004 (reverts with
 * them): return data shorter than a word. Memory holds 0xee at 0xc3, where
 * the copied bytes' padding begins. *)
Definition short_return_state_def:
  short_return_state =
    (memory_write 0xc3 [0xeew] initial_state) with world := (initial_state.world with accounts :=
      update_account 0x5004w
        (empty_account_state with
           code := [0x62w; 1w; 2w; 3w; 0x60w; 0w; 0x52w; 0x60w; 3w; 0x60w; 0x1dw; 0xfdw])
        (update_account 0x5003w
           (empty_account_state with
              code := [0x62w; 1w; 2w; 3w; 0x60w; 0w; 0x52w; 0x60w; 3w; 0x60w; 0x1dw; 0xf3w])
           empty_accounts))
End

(* Bind low-level return bytes directly; a try's raw failure data is
 * materialized by the generic catch before the block reads it. *)
Definition return_bytes_proc_def:
  return_bytes_proc op code = <|
    procedure_id := AstId 150;
    parameters := [];
    return_bindings := [(AstId 154, u256)];
    body := [
      DefineStmt (AstId 151) (SingleType (LocatedT MemoryLoc BytesT))
        (BytesLiteralOperation BytesT []);
      DefineStmt (AstId 152)
        (ProductType [SingleType BoolT;
          case op of TryExternalCallOperation _ _ _ _ _ _ _ _ => RevertDataType
                   | _ => SingleType (LocatedT MemoryLoc BytesT)]) op] ++
      (case op of
         TryExternalCallOperation _ _ _ _ _ _ _ _ =>
           [DefineStmt (AstId 155) RevertDataType
              (TupleComponentOperation 1 (BoundAtom (AstId 152)));
            DefineStmt (AstId 153) (SingleType (LocatedT MemoryLoc BytesT))
              (MaterializeRevertDataOperation (BoundAtom (AstId 155)))]
       | _ =>
           [DefineStmt (AstId 153) (SingleType (LocatedT MemoryLoc BytesT))
              (TupleComponentOperation 1 (BoundAtom (AstId 152)))]) ++
      [AssemblyStmt code [("b", AssemblyMemory (AstId 153) BytesT);
                         ("r", AssemblyLocal (AstId 154) u256)];
      ReturnStmt [BoundAtom (AstId 154)]]
  |>
End

Definition run_return_bytes_def:
  run_return_bytes op code =
    let env = core_program_environment <|
      unsupported_procedures := []; procedures := [return_bytes_proc op code];
      struct_layouts := []; function_ids := []; type_declarations := [];
      state_variables := []; immutables := [];
      entry_procedure := AstId 150;
      external_functions := []; receive_procedure := NONE;
      fallback_procedure := NONE; creation_procedure := NONE |> in
    (invoke_source 20 env (AstId 150) [] short_return_state []).completion
End

Definition short_static_def:
  short_static =
    LowLevelCallOperation ExternalStaticCall (ConstantAtom (AddressValue 0x5003w)) (k 0)
      NONE (BoundAtom (AstId 151))
End

Definition short_try_def:
  short_try =
    TryExternalCallOperation ExternalCall [1w; 2w; 3w; 4w] [] []
      (ConstantAtom (AddressValue 0x5004w)) (k 0) NONE []
End

(* Reads b's last data word, padding included; copies its three bytes. *)
Definition read_last_word_def:
  read_last_word =
    [YulAssign ["r"] (YulBuiltin YMLoad [yadd (YulName "b") (ylit 32w)])]
End

Definition copy_data_def:
  copy_data =
    [YulExprStmt (YulBuiltin YMStore [ylit 0w; ylit 0w]);
     YulExprStmt (YulBuiltin YMCopy [ylit 0w; yadd (YulName "b") (ylit 32w); ylit 3w]);
     YulAssign ["r"] (YulBuiltin YShr [ylit 232w; YulBuiltin YMLoad [ylit 0w]])]
End

val () = cv_auto_trans short_return_state_def;
val () = cv_auto_trans short_static_def;
val () = cv_auto_trans short_try_def;
val () = cv_auto_trans read_last_word_def;
val () = cv_auto_trans copy_data_def;
val () = cv_auto_trans run_return_bytes_def;

(* Bytes copied from return data, a staticcall's or a caught revert's, leave
 * their padding as memory held it, here the 0xee at 0xc3: nothing wrote
 * there, the call's selector having gone below the copy's data. *)
Theorem asm_return_data_padding:
  run_return_bytes short_static read_last_word =
    ReturnCompletion [ScalarValue (IntegerValue (0x010203ee * 2 ** 224))] ∧
  run_return_bytes short_static copy_data =
    ReturnCompletion [ScalarValue (IntegerValue 0x010203)] ∧
  run_return_bytes short_try read_last_word =
    ReturnCompletion [ScalarValue (IntegerValue (0x010203ee * 2 ** 224))] ∧
  run_return_bytes short_try copy_data =
    ReturnCompletion [ScalarValue (IntegerValue 0x010203)]
Proof
  CONV_TAC cv_eval
QED

Definition transient_counter_run_def:
  transient_counter_run st x =
    invoke_source 10
      (core_program_environment (storage_program [counter with state_backend := TransientStorage]))
      (AstId 20) [ScalarValue (IntegerValue x)] st []
End

Definition transient_counter_state_def:
  transient_counter_state = initial_state with world := initial_state.world with
    transient := update_transient_storage 0w (update_storage 0w 0xaabbccw empty_storage)
      (update_transient_storage 7w (update_storage 0w 123w empty_storage)
        empty_transient_storage)
End

val () = cv_auto_trans transient_counter_run_def;
val () = cv_auto_trans transient_counter_state_def;

Theorem transient_scalar_writes_preserve_other_bytes_and_accounts:
  (transient_counter_run transient_counter_state 5).completion =
    ReturnCompletion [ScalarValue (IntegerValue 5)] ∧
  lookup_storage 0w (lookup_transient_storage 0w
    (transient_counter_run transient_counter_state 5).state.world.transient) = 0xaa05ccw ∧
  lookup_storage 0w (lookup_transient_storage 7w
    (transient_counter_run transient_counter_state 5).state.world.transient) = 123w ∧
  lookup_storage 0w (lookup_account 0w
    (transient_counter_run transient_counter_state 5).state.world.accounts).storage = 0w
Proof
  CONV_TAC cv_eval
QED

Theorem transient_static_write_rejected:
  (transient_counter_run static_state 5).completion = InvalidCompletion "bad scalar write"
Proof
  CONV_TAC cv_eval
QED

Theorem transient_aggregate_state_rejected:
  storage_wf [counter with state_backend := TransientStorage] ∧
  wf_core_state_variable (core_program_environment (storage_program []))
    (counter with <| state_type := MappingT (UintT 256) (UintT 8);
      state_offset := 0 |>) ∧
  ¬wf_core_state_variable (core_program_environment (storage_program []))
    (counter with <| state_backend := TransientStorage;
      state_type := MappingT (UintT 256) (UintT 8); state_offset := 0 |>)
Proof
  EVAL_TAC
QED

(* Canonical packed values survive their neighboring bytes; invalid bool and
 * enum bytes fail closed in transient storage just as in persistent storage. *)
Definition transient_read_test_def:
  transient_read_test word ty =
    read_storage_reference
      (core_program_environment (storage_program [] with
        type_declarations := [(AstId 900, EnumDeclaration 3)]))
      (initial_state.world with transient :=
        update_transient_storage 7w (update_storage 3w word empty_storage)
          empty_transient_storage)
      ty (StorageReference TransientStorage 7w 3w 1 ty (LayoutId 0))
End

val () = cv_auto_trans transient_read_test_def;

Theorem transient_bool_reads_fail_closed:
  transient_read_test 0xaa0000w BoolT = ValueOk (ScalarValue (BoolValue F)) ∧
  transient_read_test 0xaa0100w BoolT = ValueOk (ScalarValue (BoolValue T)) ∧
  transient_read_test 0xaa0200w BoolT =
    ValueAbrupt (InvalidCompletion "bad storage read") ∧
  transient_read_test 0xaaff00w BoolT =
    ValueAbrupt (InvalidCompletion "bad storage read")
Proof
  CONV_TAC cv_eval
QED

Theorem transient_enum_reads_fail_closed:
  transient_read_test 0xaa0000w (EnumT (AstId 900)) =
    ValueOk (ScalarValue (IntegerValue 0)) ∧
  transient_read_test 0xaa0200w (EnumT (AstId 900)) =
    ValueOk (ScalarValue (IntegerValue 2)) ∧
  transient_read_test 0xaa0300w (EnumT (AstId 900)) =
    ValueAbrupt (InvalidCompletion "bad storage read") ∧
  transient_read_test 0xaaff00w (EnumT (AstId 900)) =
    ValueAbrupt (InvalidCompletion "bad storage read")
Proof
  CONV_TAC cv_eval
QED

(* Return data across the source and its blocks: a procedure running the
 * statements pre and then one block per code, each with x bound to its
 * parameter, against call_state's callees. *)
Definition rd_proc_def:
  rd_proc pre codes = <|
    procedure_id := AstId 130;
    parameters := [(AstId 131, u256)];
    return_bindings := [(AstId 132, u256)];
    body := pre ++
      MAP (λc. AssemblyStmt c [("x", AssemblyLocal (AstId 131) u256)]) codes ++
      [ReturnStmt [BoundAtom (AstId 131)]]
  |>
End

Definition run_rd_def:
  run_rd pre codes =
    (invoke_source 20 (core_program_environment <|
        unsupported_procedures := []; procedures := [rd_proc pre codes];
        struct_layouts := []; function_ids := []; type_declarations := [];
        state_variables := []; immutables := [];
        entry_procedure := AstId 130;
        external_functions := []; receive_procedure := NONE;
        fallback_procedure := NONE; creation_procedure := NONE |>)
      (AstId 130) [ScalarValue (IntegerValue 7)] call_state []).completion
End

(* A high-level call to 0x5000 (returns a word), a try call to 0x5001
 * (reverts with a word, caught), a low-level call to 0x5000, and an
 * ecrecover of an invalid signature. *)
Definition rd_high_def:
  rd_high =
    DefineStmt (AstId 133) (SingleType u256)
      (ExternalCallOperation ExternalCall [1w; 2w; 3w; 4w] [] [u256]
         (ConstantAtom (AddressValue 0x5000w)) (k 0) NONE [])
End

Definition rd_try_def:
  rd_try =
    DefineStmt (AstId 134)
      (ProductType [SingleType BoolT; SingleType u256;
                    SingleType (LocatedT MemoryLoc BytesT)])
      (TryExternalCallOperation ExternalCall [1w; 2w; 3w; 4w] [] [u256]
         (ConstantAtom (AddressValue 0x5001w)) (k 0) NONE [])
End

Definition rd_low_def:
  rd_low =
    DefineStmt (AstId 135)
      (ProductType [SingleType BoolT; SingleType (LocatedT MemoryLoc BytesT)])
      (LowLevelCallOperation ExternalCall (ConstantAtom (AddressValue 0x5000w))
         (k 0) NONE (ConstantAtom (BytesValue [])))
End

Definition rd_ecrecover_def:
  rd_ecrecover =
    DefineStmt (AstId 136) (SingleType (AddressT NonpayableAddress))
      (BuiltinOperation EcrecoverBuiltin
         [ConstantAtom (BytesValue (REPLICATE 32 0w)); k 27;
          ConstantAtom (BytesValue (REPLICATE 32 0w));
          ConstantAtom (BytesValue (REPLICATE 32 0w))])
End

Definition rd_size_def:
  rd_size = [YulAssign ["x"] (YulBuiltin YReturnDataSize [])]
End

Definition rd_bubble_def:
  rd_bubble =
    [YulLet ["p"] (SOME (YulBuiltin YMLoad [ylit 0x40w]));
     YulExprStmt (YulBuiltin YReturnDataCopy
       [YulName "p"; ylit 0w; YulBuiltin YReturnDataSize []]);
     YulExprStmt (YulBuiltin YRevert [YulName "p"; YulBuiltin YReturnDataSize []])]
End

Definition rd_no_call_def:
  rd_no_call = [YulAssign ["x"] (YulBuiltin YAdd [YulName "x"; ylit 1w])]
End

Definition rd_call_def:
  rd_call a = [YulExprStmt (YulBuiltin YPop [ycall (ylit a) 0w 0w 0w 0w])]
End

val () = cv_auto_trans run_rd_def;
val () = List.app cv_auto_trans
  [rd_high_def, rd_try_def, rd_low_def, rd_ecrecover_def, rd_size_def,
   rd_bubble_def, rd_no_call_def, rd_call_def];

(* A frame starts with no return data; each call of the source leaves its
 * callee's return or revert bytes, the caught revert of a try included, and
 * a block keeps them for the next. *)
Theorem asm_return_data_known:
  run_rd [] [rd_size] = ReturnCompletion [ScalarValue (IntegerValue 0)] ∧
  run_rd [rd_high] [rd_size] = ReturnCompletion [ScalarValue (IntegerValue 32)] ∧
  run_rd [rd_low] [rd_size] = ReturnCompletion [ScalarValue (IntegerValue 32)] ∧
  run_rd [rd_try] [rd_size] = ReturnCompletion [ScalarValue (IntegerValue 32)] ∧
  run_rd [rd_try] [rd_bubble] = RevertCompletion (REPLICATE 31 0w ++ [0xaaw]) ∧
  run_rd [rd_high] [rd_no_call; rd_size] =
    ReturnCompletion [ScalarValue (IntegerValue 32)] ∧
  run_rd [] [rd_call 0x5000w; rd_size] =
    ReturnCompletion [ScalarValue (IntegerValue 32)]
Proof
  CONV_TAC cv_eval
QED

(* After an ecrecover the source does not know the return data: a block that
 * could read it before a call of its own fails closed, also after a block
 * that made no call or a call that returned nothing; a call that returned
 * bytes makes it known again. *)
Theorem asm_return_data_unknown:
  run_rd [rd_ecrecover] [rd_size] =
    InvalidCompletion "assembly reads return data the source does not know" ∧
  run_rd [rd_high; rd_ecrecover] [rd_size] =
    InvalidCompletion "assembly reads return data the source does not know" ∧
  run_rd [rd_ecrecover] [rd_no_call; rd_size] =
    InvalidCompletion "assembly reads return data the source does not know" ∧
  run_rd [rd_ecrecover] [rd_call 0x5002w; rd_size] =
    InvalidCompletion "assembly reads return data the source does not know" ∧
  run_rd [rd_ecrecover] [rd_call 0x5000w ++ rd_size] =
    ReturnCompletion [ScalarValue (IntegerValue 32)] ∧
  run_rd [rd_ecrecover] [rd_call 0x5000w; rd_size] =
    ReturnCompletion [ScalarValue (IntegerValue 32)]
Proof
  CONV_TAC cv_eval
QED

(* sha256, which the compiler computes by calling the precompile at address
 * 2, leaves return data unknown as ecrecover does; blockhash, an opcode,
 * keeps what the last call left. *)
Definition rd_sha256_def:
  rd_sha256 =
    [DefineStmt (AstId 137) (SingleType (LocatedT MemoryLoc BytesT))
       (DefaultReferenceOperation MemoryLoc BytesT);
     DefineStmt (AstId 138) (SingleType (FixedBytesT 32))
       (BuiltinOperation Sha256Builtin [BoundAtom (AstId 137)])]
End

Definition rd_blockhash_def:
  rd_blockhash =
    DefineStmt (AstId 139) (SingleType (FixedBytesT 32))
      (BuiltinOperation BlockhashBuiltin [k 0])
End

val () = List.app cv_auto_trans [rd_sha256_def, rd_blockhash_def];

Theorem asm_return_data_precompile_builtins:
  run_rd (rd_high :: rd_sha256) [rd_size] =
    InvalidCompletion "assembly reads return data the source does not know" ∧
  run_rd [rd_high; rd_blockhash] [rd_size] =
    ReturnCompletion [ScalarValue (IntegerValue 32)]
Proof
  CONV_TAC cv_eval
QED

(* The static rule admits return data reads before a call of the block's own,
 * in a Yul function's body too. Value gas() uses explicit observations. *)
Theorem asm_gas_rule:
  assembly_gas_ok rd_size ∧
  assembly_gas_ok rd_bubble ∧
  assembly_gas_ok [YulFunction "f" [] ["r"]
                      [YulAssign ["r"] (YulBuiltin YReturnDataSize [])]] ∧
  assembly_gas_ok [YulAssign ["x"] (YulBuiltin YGas [])]
Proof
  EVAL_TAC
QED

(* Storage pointers. run_asm_pointer runs a block with the pointer parameter
 * p as "p.slot" and "p.offset" and the local r, from an account at address
 * 5, and returns r and p. *)
Definition asm_pointer_proc_def:
  asm_pointer_proc code = <|
    procedure_id := AstId 160;
    parameters := [(AstId 161, LocatedT StorageLoc (ArrayT u256 NONE))];
    return_bindings := [(AstId 162, u256)];
    body := [AssemblyStmt code [("r", AssemblyLocal (AstId 162) u256);
                                ("p.slot", AssemblyPointerSlot (AstId 161));
                                ("p.offset", AssemblyPointerOffset (AstId 161))];
             ReturnStmt [BoundAtom (AstId 162); BoundAtom (AstId 161)]]
  |>
End

Definition run_asm_pointer_def:
  run_asm_pointer code p =
    let env = core_program_environment <|
      unsupported_procedures := []; procedures := [asm_pointer_proc code];
      struct_layouts := []; function_ids := []; type_declarations := [];
      state_variables := []; immutables := [];
      entry_procedure := AstId 160;
      external_functions := []; receive_procedure := NONE;
      fallback_procedure := NONE; creation_procedure := NONE |> in
    let st = initial_state with frame := initial_state.frame with self_address := 5w in
    (invoke_source 20 env (AstId 160) [p] st []).completion
End

val () = cv_auto_trans run_asm_pointer_def;

(* The block reads the pointer's slot and offset; assigning its slot rebinds
 * it to that slot of the executing account, keeping its type and layout,
 * and leaving it alone rebinds it to its own slot. A pointer that doesn't
 * hold a storage reference fails closed. *)
Theorem asm_storage_pointers:
  run_asm_pointer [YulAssign ["r"] (yadd (YulName "p.slot") (YulName "p.offset"))]
    (ReferenceValue (StorageReference PersistentStorage 5w 4w 0 (ArrayT u256 NONE)
       (LayoutId 3))) =
    ReturnCompletion [ScalarValue (IntegerValue 4);
      ReferenceValue (StorageReference PersistentStorage 5w 4w 0 (ArrayT u256 NONE)
        (LayoutId 3))] ∧
  run_asm_pointer [YulAssign ["p.slot"] (yadd (YulName "p.slot") (ylit 6w))]
    (ReferenceValue (StorageReference PersistentStorage 0w 4w 0 (ArrayT u256 NONE)
       (LayoutId 3))) =
    ReturnCompletion [ScalarValue (IntegerValue 0);
      ReferenceValue (StorageReference PersistentStorage 5w 10w 0 (ArrayT u256 NONE)
        (LayoutId 3))] ∧
  run_asm_pointer [YulAssign ["r"] (YulName "p.slot")]
    (ReferenceValue (MemoryReference 96 (ArrayT u256 NONE))) =
    InvalidCompletion "bad assembly reference"
Proof
  CONV_TAC cv_eval
QED

Definition asm_calldata_proc_def:
  asm_calldata_proc code = <|
    procedure_id := AstId 170;
    parameters := [(AstId 171, LocatedT CalldataLoc BytesT)];
    return_bindings := [(AstId 172, u256)];
    body := [AssemblyStmt code [("r", AssemblyLocal (AstId 172) u256);
                                ("b.offset", AssemblyCalldataOffset (AstId 171));
                                ("b.length", AssemblyCalldataLength (AstId 171))];
             ReturnStmt [BoundAtom (AstId 172); BoundAtom (AstId 171)]]
  |>
End

Definition run_asm_calldata_def:
  run_asm_calldata code b =
    let env = core_program_environment <|
      unsupported_procedures := []; procedures := [asm_calldata_proc code];
      struct_layouts := []; function_ids := []; type_declarations := [];
      state_variables := []; immutables := [];
      entry_procedure := AstId 170;
      external_functions := []; receive_procedure := NONE;
      fallback_procedure := NONE; creation_procedure := NONE |> in
    let st = initial_state with frame :=
               initial_state.frame with call_data := REPLICATE 100 0w in
    (invoke_source 20 env (AstId 170) [b] st []).completion
End

val () = cv_auto_trans run_asm_calldata_def;

(* The block reads a calldata reference's offset and length and may rebind
 * both, keeping its type; a slice it leaves past the end of the calldata
 * fails closed, and so does a local that doesn't hold a calldata reference. *)
Theorem asm_calldata_references:
  run_asm_calldata [YulAssign ["r"] (yadd (YulName "b.offset") (YulName "b.length"))]
    (ReferenceValue (CalldataReference 4 64 BytesT)) =
    ReturnCompletion [ScalarValue (IntegerValue 68);
      ReferenceValue (CalldataReference 4 64 BytesT)] ∧
  run_asm_calldata [YulAssign ["b.offset"] (yadd (YulName "b.offset") (ylit 32w));
                    YulAssign ["b.length"] (ylit 10w)]
    (ReferenceValue (CalldataReference 4 64 BytesT)) =
    ReturnCompletion [ScalarValue (IntegerValue 0);
      ReferenceValue (CalldataReference 36 10 BytesT)] ∧
  run_asm_calldata [YulAssign ["b.length"] (ylit 200w)]
    (ReferenceValue (CalldataReference 4 64 BytesT)) =
    InvalidCompletion "assembly left a calldata reference outside the calldata" ∧
  run_asm_calldata [YulAssign ["r"] (YulName "b.length")]
    (ReferenceValue (MemoryReference 96 BytesT)) =
    InvalidCompletion "bad assembly reference"
Proof
  CONV_TAC cv_eval
QED

Definition recursive_reset_env_def:
  recursive_reset_env = test_env with <|
    type_declarations := [(AstId 900, StructDeclaration
      [(AstId 901, UintT 8); (AstId 902, ArrayT (StructT (AstId 900)) NONE)])];
    struct_layouts := [(AstId 900, <| struct_id := AstId 900; struct_slots := 2;
      struct_fields :=
        [<| state_id := AstId 901; state_type := UintT 8;
            state_backend := PersistentStorage; state_slot := 0w; state_offset := 0 |>;
         <| state_id := AstId 902; state_type := ArrayT (StructT (AstId 900)) NONE;
            state_backend := PersistentStorage; state_slot := 1w; state_offset := 0 |>] |>)]
  |>
End

Definition recursive_reset_state_def:
  recursive_reset_state = initial_state with <|
    world := initial_state.world with accounts :=
      set_storage_word (set_storage_word (set_storage_word empty_accounts 0w 11w 7w)
        0w 12w 1w) 0w (mapping_slot [] 12w) 8w;
    targets := FEMPTY |+ (ast_key (AstId 1), ValueTarget
      (StorageReference PersistentStorage 0w 11w 0 (StructT (AstId 900)) (LayoutId 0)))
  |>
End

val () = cv_auto_trans recursive_reset_env_def;
val () = cv_auto_trans recursive_reset_state_def;

Theorem recursive_reset_exhaustion_is_not_invalid:
  (reset_target 0 recursive_reset_env (AstId 1) (StructT (AstId 900))
     recursive_reset_state []).completion = FuelExhausted
Proof
  CONV_TAC cv_eval
QED

Theorem recursive_reset_with_more_fuel_completes:
  (reset_target 1 recursive_reset_env (AstId 1) (StructT (AstId 900))
     recursive_reset_state []).completion = NormalCompletion ∧
  reset_target 1 recursive_reset_env (AstId 1) (StructT (AstId 900))
     recursive_reset_state [] =
  reset_target 20 recursive_reset_env (AstId 1) (StructT (AstId 900))
     recursive_reset_state []
Proof
  CONV_TAC cv_eval
QED

Theorem reset_storage_in_static_frame_fails:
  (reset_target 1 recursive_reset_env (AstId 1) (StructT (AstId 900))
     (recursive_reset_state with frame := recursive_reset_state.frame with static_context := T)
     []).completion = InvalidCompletion "storage reset in static frame"
Proof
  CONV_TAC cv_eval
QED

Definition calldata_head_env_def:
  calldata_head_env = recursive_reset_env with type_declarations :=
    [(AstId 950, StructDeclaration [(AstId 951, UintT 8); (AstId 952, BytesT)])]
End

Definition calldata_head_scopes_def:
  calldata_head_scopes ty offset =
    [FEMPTY |+ (1, <| binding_type := SingleType (LocatedT CalldataLoc ty);
      binding_value := ReferenceValue (CalldataReference offset 0 ty) |>)]
End

val () = cv_auto_trans calldata_head_env_def;
val () = cv_auto_trans calldata_head_scopes_def;

Theorem assembly_calldata_requires_complete_object_head:
  EVERY (λty.
    assembly_calldata_ok calldata_head_env (REPLICATE 64 0w)
      (calldata_head_scopes ty 0) [("p", AssemblyCalldataOffset (AstId 1))] ∧
    ¬assembly_calldata_ok calldata_head_env (REPLICATE 63 0w)
      (calldata_head_scopes ty 0) [("p", AssemblyCalldataOffset (AstId 1))] ∧
    ¬assembly_calldata_ok calldata_head_env (REPLICATE 64 0w)
      (calldata_head_scopes ty 64) [("p", AssemblyCalldataOffset (AstId 1))])
    [StructT (AstId 950); ArrayT BytesT (SOME 2)]
Proof
  EVAL_TAC
QED

Definition gas_reads_def:
  gas_reads gas =
    eval_block 20 test_env
      [DefineStmt (AstId 900) (SingleType u256) (EnvironmentOperation GasLeft);
       DefineStmt (AstId 901) (SingleType u256) (EnvironmentOperation GasLeft);
       ReturnStmt [BoundAtom (AstId 900); BoundAtom (AstId 901)]]
      (initial_state with scopes := [FEMPTY]) gas
End

val () = cv_auto_trans gas_reads_def;

Theorem gas_reads_in_order:
  (gas_reads [GasLeftObservation 100; GasLeftObservation 80]).completion =
    ReturnCompletion [ScalarValue (IntegerValue 100); ScalarValue (IntegerValue 80)] ∧
  (gas_reads [GasLeftObservation 100; GasLeftObservation 80]).unused_gas_evidence = []
Proof
  CONV_TAC cv_eval
QED

Theorem gas_reads_fail_closed:
  (gas_reads []).completion = InvalidCompletion "missing gasleft observation" ∧
  (gas_reads [GasLeftObservation 100]).completion =
    InvalidCompletion "missing gasleft observation" ∧
  (gas_reads [GasLeftObservation (2 ** 256)]).completion =
    InvalidCompletion "missing gasleft observation" ∧
  (gas_reads [CallGasObservation 100]).completion =
    InvalidCompletion "missing gasleft observation"
Proof
  CONV_TAC cv_eval
QED

Definition assembly_gas_read_def:
  assembly_gas_read gas =
    invoke_source 20 (asm_env [YulAssign ["x"] (YulBuiltin YGas [])])
      (AstId 110) [ScalarValue (IntegerValue 7)] initial_state gas
End

val () = cv_auto_trans assembly_gas_read_def;

Theorem assembly_gas_consumes_one:
  (assembly_gas_read [GasLeftObservation 123; GasLeftObservation 99]).completion =
    ReturnCompletion [ScalarValue (IntegerValue 123)] ∧
  (assembly_gas_read [GasLeftObservation 123; GasLeftObservation 99]).unused_gas_evidence =
    [GasLeftObservation 99] ∧
  (assembly_gas_read []).completion = InvalidCompletion "missing gas observation" ∧
  (assembly_gas_read [GasLeftObservation (2 ** 256)]).completion =
    InvalidCompletion "missing gas observation" ∧
  (assembly_gas_read [CreateGasObservation 123]).completion =
    InvalidCompletion "missing gas observation"
Proof
  CONV_TAC cv_eval
QED

(* A bare gas() as create's or create2's value is a gas reading, not the
 * budget a call's first operand means: it consumes an observation. *)
Definition creation_gas_read_def:
  creation_gas_read op gas =
    invoke_source 20 (asm_env [YulAssign ["x"]
        (YulBuiltin op ([YulBuiltin YGas []; ylit 0w; ylit 0w] ++
                        (if op = YCreate2 then [ylit 0w] else [])))])
      (AstId 110) [ScalarValue (IntegerValue 7)] initial_state gas
End

val () = cv_auto_trans creation_gas_read_def;

Theorem creation_value_gas_is_an_observation:
  (creation_gas_read YCreate []).completion =
    InvalidCompletion "missing gas observation" ∧
  (creation_gas_read YCreate2 []).completion =
    InvalidCompletion "missing gas observation" ∧
  (creation_gas_read YCreate [GasLeftObservation 0; GasLeftObservation 5]).unused_gas_evidence =
    [GasLeftObservation 5] ∧
  (creation_gas_read YCreate2 [GasLeftObservation 0; GasLeftObservation 5]).unused_gas_evidence =
    [GasLeftObservation 5]
Proof
  CONV_TAC cv_eval
QED

Definition abort_code_def:
  abort_code =
    [store_x;
     YulExprStmt (YulBuiltin YTStore [ylit 1w; ylit 99w]);
     YulExprStmt (YulBuiltin YLog0 [ylit 0w; ylit 0w]);
     YulExprStmt (YulBuiltin YInvalid [])]
End

val () = cv_auto_trans abort_code_def;

Theorem invalid_restores_complete_world:
  run_entry 20 (asm_env abort_code) (asm_proc abort_code)
    [ScalarValue (IntegerValue 7)] initial_state.frame initial_state.world (SOME FEMPTY) 0 NONE CallEntry =
    ContractAborted initial_state.world
Proof
  CONV_TAC cv_eval
QED

Theorem unused_observation_fails_on_halt:
  run_entry_with_gas 20 (asm_env []) halt_proc [] initial_state.frame
    initial_state.world (SOME FEMPTY) 0 NONE CallEntry [GasLeftObservation 1] =
    ContractInvalid "unconsumed gas observation"
Proof
  CONV_TAC cv_eval
QED

Theorem message_signature_is_padded_calldata_prefix:
  environment_value initial_state.frame MsgSig =
    ValueOk (ScalarValue (BytesValue [0w; 0w; 0w; 0w])) ∧
  environment_value (initial_state.frame with call_data := [0x12w; 0x34w]) MsgSig =
    ValueOk (ScalarValue (BytesValue [0x12w; 0x34w; 0w; 0w])) ∧
  environment_value
    (initial_state.frame with call_data := [1w; 2w; 3w; 4w; 5w]) MsgSig =
    ValueOk (ScalarValue (BytesValue [1w; 2w; 3w; 4w]))
Proof
  EVAL_TAC
QED

(* block.prevrandao and block.difficulty read the transaction's prevRandao,
   all 256 bits of it. *)
Theorem block_prevrandao_reads_prev_randao:
  environment_value
    (initial_state.frame with tx_params :=
       initial_state.frame.tx_params with
         prevRandao := 0x8000000000000000000000000000000000000000000000000000000000000001w)
    BlockPrevRandao =
    ValueOk (ScalarValue (IntegerValue (2 ** 255 + 1)))
Proof
  EVAL_TAC
QED

Theorem calldata_reference_defaults:
  eval_operation test_env initial_state
    (DefaultReferenceOperation CalldataLoc (ArrayT u256 (SOME 2))) =
    INL (ReferenceValue (CalldataReference 0 2 (ArrayT u256 (SOME 2))), initial_state) ∧
  eval_operation test_env initial_state
    (DefaultReferenceOperation CalldataLoc BytesT) =
    INL (ReferenceValue (CalldataReference 0 0 BytesT), initial_state) ∧
  eval_operation test_env initial_state
    (DefaultReferenceOperation CalldataLoc u256) =
    INR (InvalidCompletion "bad reference default")
Proof
  EVAL_TAC
QED

Theorem storage_reference_defaults:
  eval_operation test_env initial_state
    (DefaultReferenceOperation StorageLoc (ArrayT u256 NONE)) =
    INL (ReferenceValue
      (StorageReference PersistentStorage 0w 0w 0 (ArrayT u256 NONE) (LayoutId 0)),
      initial_state) ∧
  eval_operation test_env initial_state
    (DefaultReferenceOperation StorageLoc (MappingT u256 u256)) =
    INL (ReferenceValue
      (StorageReference PersistentStorage 0w 0w 0 (MappingT u256 u256) (LayoutId 0)),
      initial_state) ∧
  eval_operation test_env initial_state
    (DefaultReferenceOperation StorageLoc u256) =
    INR (InvalidCompletion "bad reference default")
Proof
  EVAL_TAC
QED

(* Event hash preimages written one after another at the free memory pointer,
 * which starts at p. *)
Definition preimages_moved_def:
  preimages_moved p temps =
    FST (write_at_each temps (memory_store 64 p initial_state))
End

val () = cv_auto_trans preimages_moved_def;

(* A preimage that moves the pointer counts even when the next one, written
 * where it moved, moves it back. *)
Theorem preimage_restoring_the_pointer_still_moved_it:
  preimages_moved 64 [REPLICATE 32 0w; REPLICATE 64 0w ++ num_to_bytes 32 64] ∧
  ¬preimages_moved 128 [REPLICATE 64 1w; REPLICATE 32 2w]
Proof
  CONV_TAC cv_eval
QED

