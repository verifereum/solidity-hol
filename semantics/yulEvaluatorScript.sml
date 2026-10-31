(* The Yul evaluator: a fuel-indexed, executable interpreter for the runtime
 * object, written so that it cv_evals.
 *
 * Fuel: n bounds every recursive step that is not structural. Sibling
 * statements and the arguments of one call reuse the bound; entering a
 * function takes one off, and a loop's back edge takes one off, so
 * straight-line code and a loop's first iteration need none. The 257th nested
 * call, or the n+1th iteration of one loop, ends in YulOutOfFuel rather than
 * in a wrong answer.
 *
 * Scopes: a block, an if branch, a switch case, a loop body, a loop's post
 * statement and a call each run in a pushed scope; leaving pops exactly that
 * scope, so writes to enclosing bindings survive and a branch's locals do not.
 * A for loop's prelude runs in the loop's own scope, which is why its variable
 * is visible in the condition, body and post statement.
 *
 * Order: a call's arguments are evaluated right to left, as Yul specifies, and
 * case values are tried in order.
 *
 * Values: expressions produce a list of 256-bit words, since a call to a
 * user-defined function can return several. Binding or returning the wrong
 * number of them is an error rather than a silent truncation, as is a literal
 * too long for the dialect, an unknown function, an unbound name, a builtin
 * called with the wrong number of arguments, and the object-level builtins,
 * which a runtime object never contains.
 *
 * Memory, storage, calls and logs: the builtins that read or write them are in
 * eval_yul_builtin below, on the machine in yulState. Memory is byte-addressed
 * and every access raises its active size. Nothing here reads gas.
 *)
Theory yulEvaluator
Ancestors
  yulAST yulState yulDialect vfmState vfmConstants vfmExecution keccak
  cv_string_fmap
Libs
  cv_transLib wordsLib

(* Scopes *)

Definition yul_push_scope_def:
  yul_push_scope m =
    m with scopes := (FEMPTY : string |-> bytes32) :: m.scopes
End

Definition yul_pop_scope_def:
  yul_pop_scope m = m with scopes := TL m.scopes
End

(* Results *)

Definition yul_normal_def:
  yul_normal m = <| completion := YulNormal; machine := m |>
End

Definition yul_abrupt_def:
  yul_abrupt c m = <| completion := c; machine := m |>
End

Definition yul_invalid_def:
  yul_invalid reason m = yul_abrupt (YulInvalid reason) m
End

Definition yul_pop_result_def:
  yul_pop_result (r : yul_result) =
    r with machine := yul_pop_scope r.machine
End

(* The scope and binding types are pinned rather than left to inference: a
 * polymorphic finite-map argument is not something the cv translation can
 * encode, and these are the only scopes this machine has.
 *)
Definition yul_lookup_def:
  (yul_lookup (x : string) [] = NONE) ∧
  (yul_lookup (x : string) ((scope : string |-> bytes32) :: rest) =
    case FLOOKUP scope x of SOME v => SOME v | NONE => yul_lookup x rest)
End

Definition yul_lookup_names_def:
  (yul_lookup_names [] scopes = SOME []) ∧
  (yul_lookup_names (x :: xs) scopes =
    case yul_lookup x scopes of
      NONE => NONE
    | SOME v =>
        (case yul_lookup_names xs scopes of
           NONE => NONE
         | SOME vs => SOME (v :: vs)))
End

(* Writing bindings into a scope, a pair at a time: the later pair of a name
 * wins, as FUPDATE_LIST would.  Spelled out rather than left to FUPDATE_LIST
 * because that operation's cv equation is conditional, which the cv
 * translation of a non-recursive definition cannot discharge.
 *)
Definition yul_bind_scope_def:
  (yul_bind_scope (scope : string |-> bytes32) [] = scope) ∧
  (yul_bind_scope (scope : string |-> bytes32) ((x, v) :: ps) =
     yul_bind_scope (scope |+ (x, v)) ps)
End

(* Binds names in the innermost scope.  Written as a case on the scope stack
 * rather than with HD and TL, whose cv equations carry a non-emptiness
 * condition a translated definition cannot discharge.
 *)
Definition yul_bind_def:
  yul_bind names values m =
    if LENGTH names ≠ LENGTH values then yul_invalid "bad binding" m
    else
      case m.scopes of
        [] => yul_invalid "bad binding" m
      | scope :: rest =>
          yul_normal (m with scopes :=
            yul_bind_scope scope (ZIP (names, values)) :: rest)
End

(* Updates the innermost scope that binds x. *)
Definition yul_update_def:
  (yul_update (x : string) (v : bytes32) [] = NONE) ∧
  (yul_update (x : string) (v : bytes32)
     ((scope : string |-> bytes32) :: rest) =
    if FLOOKUP scope x = NONE then
      case yul_update x v rest of
        NONE => NONE
      | SOME rest' => SOME (scope :: rest')
    else SOME ((scope |+ (x, v)) :: rest))
End

Definition yul_assign_list_def:
  (yul_assign_list [] (rest : (string |-> bytes32) list) = SOME rest) ∧
  (yul_assign_list ((x, v) :: ps) (rest : (string |-> bytes32) list) =
    case yul_update x v rest of
      NONE => NONE
    | SOME rest' => yul_assign_list ps rest')
End

Definition yul_assign_def:
  yul_assign names values m =
    if LENGTH names ≠ LENGTH values then yul_invalid "bad assignment" m
    else
      case yul_assign_list (ZIP (names, values)) m.scopes of
        NONE => yul_invalid "unbound assignment" m
      | SOME scopes => yul_normal (m with scopes := scopes)
End

(* Memory: a byte per address, absent bytes being zero, with the active size
 * beside it.  Every access raises the size to the end of the last word it
 * touches, and an access of no bytes touches nothing, as in the EVM.
 *)

Definition yul_memory_byte_def:
  yul_memory_byte m (a : num) =
    case FLOOKUP m.memory a of NONE => 0w | SOME b => b
End

Definition yul_memory_read_def:
  yul_memory_read m offset sz =
    GENLIST (λi. yul_memory_byte m (offset + i)) sz
End

Definition yul_memory_write_def:
  yul_memory_write m offset [] = m ∧
  yul_memory_write m offset (b :: bs) =
    yul_memory_write (m with memory := m.memory |+ (offset, b)) (offset + 1) bs
End


Definition yul_memory_touch_def:
  yul_memory_touch m offset sz =
    m with memory_size :=
      MAX m.memory_size
          (if sz = 0 then 0 else word_size (offset + sz) * 32)
End

(* The touched machine and the bytes read from it. *)
Definition yul_memory_region_def:
  yul_memory_region m offset sz =
    let m' = yul_memory_touch m offset sz in
      (m', yul_memory_read m' offset sz)
End

Definition yul_mload_def:
  yul_mload m offset =
    yul_memory_region m offset 32
End

Definition yul_mstore_def:
  yul_mstore m offset value =
    yul_memory_write (yul_memory_touch m offset 32) offset (word_to_bytes value T)
End

(* Storage, straight to the executing account's. *)

Definition yul_sload_def:
  yul_sload m slot =
    lookup_storage slot (lookup_account m.self_address m.accounts).storage
End

Definition yul_sstore_def:
  yul_sstore m slot value =
    let account = lookup_account m.self_address m.accounts in
      m with accounts :=
        update_account m.self_address
          (account with storage := update_storage slot value account.storage)
          m.accounts
End

(* Literals *)

Definition yul_literal_value_def:
  yul_literal_value (LitNumber w) = SOME w ∧
  yul_literal_value (LitBytes bs) =
    (if LENGTH bs ≤ 32 then
       SOME (word_of_bytes T (0w : bytes32) (take_pad_0 32 bs))
     else NONE) ∧
  yul_literal_value (LitBool b) = SOME (b2w b)
End

(* Expression results: values, or an abrupt completion with the machine it
 * left behind. *)
Datatype:
  yul_expr_result
  = EvalValues (bytes32 list) yul_machine
  | EvalAbrupt yul_completion yul_machine
End

(* One builtin, on values that have already been evaluated, left to right.
 * Anything the pinned dialect does not define -- a wrong number of arguments,
 * or one of the object-level builtins, which a runtime object cannot contain
 * -- is an error rather than a silent no-op.
 *)
Definition eval_yul_builtin_def:
  eval_yul_builtin op args m =
    case (op, args) of
      (YAdd, [a; b]) => EvalValues [a + b] m
    | (YSub, [a; b]) => EvalValues [a - b] m
    | (YMul, [a; b]) => EvalValues [a * b] m
    | (YDiv, [a; b]) => EvalValues [with_zero word_div a b] m
    | (YSDiv, [a; b]) => EvalValues [with_zero word_quot a b] m
    | (YMod, [a; b]) => EvalValues [with_zero word_mod a b] m
    | (YSMod, [a; b]) => EvalValues [with_zero word_rem a b] m
    | (YExp, [a; b]) => EvalValues [word_exp a b] m
    | (YSignExtend, [a; b]) => EvalValues [sign_extend a b] m
    | (YLt, [a; b]) => EvalValues [b2w (w2n a < w2n b)] m
    | (YGt, [a; b]) => EvalValues [b2w (w2n a > w2n b)] m
    | (YSLt, [a; b]) => EvalValues [b2w (word_lt a b)] m
    | (YSGt, [a; b]) => EvalValues [b2w (word_gt a b)] m
    | (YEq, [a; b]) => EvalValues [b2w (a = b)] m
    | (YIsZero, [a]) => EvalValues [b2w (a = 0w)] m
    | (YAnd, [a; b]) => EvalValues [word_and a b] m
    | (YOr, [a; b]) => EvalValues [word_or a b] m
    | (YXor, [a; b]) => EvalValues [word_xor a b] m
    | (YNot, [a]) => EvalValues [word_1comp a] m
    | (YShl, [n; w]) => EvalValues [word_lsl w (w2n n)] m
    | (YShr, [n; w]) => EvalValues [word_lsr w (w2n n)] m
    | (YSar, [n; w]) => EvalValues [word_asr w (w2n n)] m
    | (YKeccak256, [p; s]) =>
        let (m', bs) = yul_memory_region m (w2n p) (w2n s) in
          EvalValues [word_of_bytes T (0w : bytes32) (Keccak_256_w64 bs)] m'
    | (YMLoad, [p]) =>
        let (m', bs) = yul_mload m (w2n p) in
          EvalValues [word_of_bytes T (0w : bytes32) bs] m'
    | (YMStore, [p; v]) => EvalValues [] (yul_mstore m (w2n p) v)
    | (YSLoad, [s]) => EvalValues [yul_sload m s] m
    | (YSStore, [s; v]) => EvalValues [] (yul_sstore m s v)
    | (YCallDataLoad, [i]) =>
        EvalValues
          [word_of_bytes T (0w : bytes32) (take_pad_0 32 (DROP (w2n i) m.call_data))]
          m
    | (YCallDataSize, []) => EvalValues [n2w (LENGTH m.call_data)] m
    | (YCallValue, []) => EvalValues [m.call_value] m
    | (YMemoryGuard, [x]) => EvalValues [x] m
    | (YLog1, [p; s; topic]) =>
        let (m', bs) = yul_memory_region m (w2n p) (w2n s) in
          EvalValues []
            (m' with logs := m'.logs ++
              [<| logger := m'.self_address; topics := [topic];
                  data := bs |>])
    | (YReturn, [p; s]) =>
        let (m', bs) = yul_memory_region m (w2n p) (w2n s) in
          EvalAbrupt (YulReturn bs) m'
    | (YRevert, [p; s]) =>
        let (m', bs) = yul_memory_region m (w2n p) (w2n s) in
          EvalAbrupt (YulRevert bs) m'
    | (YCodeCopy, _) => EvalAbrupt (YulInvalid "object-level builtin") m
    | (YDataSize, _) => EvalAbrupt (YulInvalid "object-level builtin") m
    | (YDataOffset, _) => EvalAbrupt (YulInvalid "object-level builtin") m
    | _ => EvalAbrupt (YulInvalid "bad builtin call") m
End

(* Termination measures, one per group of the mutual recursion: the relation
 * handed to WF_REL_TAC is then small, and the obligations it leaves are
 * applications of these, which the step after it reduces to arithmetic.
 *
 * Fuel comes first, since a loop's back edge and a call each spend one; the
 * second component is the size of the syntax that group has still to walk.  A
 * group's row must exceed the rows of the groups it calls, which is what the
 * constants are for: a statement's row exceeds the block rows beneath it, and
 * a block's row exceeds the rows of the statements in it.
 *)
Definition yul_measure_block_def:
  yul_measure_block (n : num, fns, ss, m) =
    (n, list_size yul_stmt_size ss + 2)
End

Definition yul_measure_stmt_def:
  yul_measure_stmt (n : num, fns, q, m) = (n, yul_stmt_size q + 2)
End

Definition yul_measure_expr_def:
  yul_measure_expr (n : num, fns, e, m) = (n, yul_expr_size e)
End

Definition yul_measure_args_def:
  yul_measure_args (n : num, fns, es, m) = (n, list_size yul_expr_size es)
End

Definition yul_measure_loop_def:
  yul_measure_loop (n : num, fns, cond, post, body, m) =
    (n, yul_expr_size cond + list_size yul_stmt_size body +
        list_size yul_stmt_size post + 2)
End

Definition yul_measure_cases_def:
  yul_measure_cases (n : num, fns, v, cases, default, m) =
    (n, list_size (pair_size yul_literal_size (list_size yul_stmt_size)) cases +
        list_size yul_stmt_size default + 3)
End

(* A call is reached through the expression that makes it, so its row only has
 * to be smaller than that one's; the fuel is what decreases. *)
Definition yul_measure_invoke_def:
  yul_measure_invoke (n : num, fns, name, args, m) = (n, 0n)
End

(* Two obligations a loop's own row leaves behind: it has to be bigger than the
 * rows of the body and the post it walks, both of which are block rows.  Its
 * room for them is its condition's size -- the condition is an expression, and
 * an expression always has a size -- so these are just arithmetic. *)
Theorem yul_measure_loop_body_lt:
  ∀b p c : num. 0 < c ⇒ b + 2 < c + (b + (p + 2))
Proof
  decide_tac
QED

Theorem yul_measure_loop_post_lt:
  ∀b p c : num. 0 < c ⇒ p + 2 < c + (b + (p + 2))
Proof
  decide_tac
QED

(* The evaluator.  n is fuel, fns the functions a call may reach. *)
Definition eval_yul_def:
  (* statement lists: siblings reuse the bound, a non-normal completion stops *)
  (eval_yul_block (n : num) (fns : string |-> yul_function) [] m =
     yul_normal m) ∧
  (eval_yul_block n fns (s :: ss) m =
     let r = eval_yul_stmt n fns s m in
       if r.completion = YulNormal then
         eval_yul_block n fns ss r.machine
       else r) ∧

  (eval_yul_stmt n fns (YulBlock ss) m =
     yul_pop_result (eval_yul_block n fns ss (yul_push_scope m))) ∧
  (* a definition has no runtime effect: yul_env collected it beforehand *)
  (eval_yul_stmt n fns (YulFunction name params results body) m =
     yul_normal m) ∧
  (eval_yul_stmt n fns (YulLet names value) m =
     case value of
       NONE => yul_bind names (REPLICATE (LENGTH names) 0w) m
     | SOME e =>
         (case eval_yul_expr n fns e m of
            EvalAbrupt c m' => yul_abrupt c m'
          | EvalValues vs m' => yul_bind names vs m')) ∧
  (eval_yul_stmt n fns (YulAssign names e) m =
     case eval_yul_expr n fns e m of
       EvalAbrupt c m' => yul_abrupt c m'
     | EvalValues vs m' => yul_assign names vs m') ∧
  (eval_yul_stmt n fns (YulIf c body) m =
     case eval_yul_expr n fns c m of
       EvalAbrupt co m' => yul_abrupt co m'
     | EvalValues [v] m' =>
         if v = 0w then yul_normal m'
         else yul_pop_result (eval_yul_block n fns body (yul_push_scope m'))
     | EvalValues _ m' => yul_invalid "condition is not one value" m') ∧
  (eval_yul_stmt n fns (YulSwitch e cases default) m =
     case eval_yul_expr n fns e m of
       EvalAbrupt co m' => yul_abrupt co m'
     | EvalValues [v] m' => eval_yul_cases n fns v cases default m'
     | EvalValues _ m' => yul_invalid "case value is not one value" m') ∧
  (* the prelude runs once, in the loop's own scope *)
  (eval_yul_stmt n fns (YulFor init cond post body) m =
     let m1 = yul_push_scope m in
     let r = eval_yul_block n fns init m1 in
       if r.completion = YulNormal then
         eval_yul_loop n fns cond post body r.machine
       else yul_pop_result r) ∧
  (eval_yul_stmt n fns YulBreak m = yul_abrupt YulBreak m) ∧
  (eval_yul_stmt n fns YulContinue m = yul_abrupt YulContinue m) ∧
  (eval_yul_stmt n fns YulLeave m = yul_abrupt YulLeave m) ∧
  (eval_yul_stmt n fns (YulExprStmt e) m =
     case eval_yul_expr n fns e m of
       EvalAbrupt c m' => yul_abrupt c m'
     | EvalValues _ m' => yul_normal m') ∧

  (eval_yul_expr n fns (YulLit l) m =
     case yul_literal_value l of
       SOME v => EvalValues [v] m
     | NONE => EvalAbrupt (YulInvalid "literal out of range") m) ∧
  (eval_yul_expr n fns (YulName x) m =
     case yul_lookup x m.scopes of
       SOME v => EvalValues [v] m
     | NONE => EvalAbrupt (YulInvalid "unbound name") m) ∧
  (eval_yul_expr n fns (YulBuiltin op args) m =
     case eval_yul_args n fns args m of
       EvalAbrupt c m' => EvalAbrupt c m'
     | EvalValues vs m' => eval_yul_builtin op vs m') ∧
  (eval_yul_expr n fns (YulApply f args) m =
     if n = 0 then EvalAbrupt YulOutOfFuel m
     else
       case eval_yul_args n fns args m of
         EvalAbrupt c m' => EvalAbrupt c m'
       | EvalValues vs m' => invoke_yul (n - 1) fns f vs m') ∧

  (* arguments right to left: the tail first, then the head *)
  (eval_yul_args n fns [] m = EvalValues [] m) ∧
  (eval_yul_args n fns (a :: args) m =
     case eval_yul_args n fns args m of
       EvalAbrupt c m' => EvalAbrupt c m'
     | EvalValues vs m' =>
         (case eval_yul_expr n fns a m' of
            EvalAbrupt c m'' => EvalAbrupt c m''
          | EvalValues w m'' => EvalValues (w ++ vs) m'')) ∧

  (* one iteration of a for loop, in the scope the prelude made; fuel is spent
   * on the back edge, so the first iteration is free *)
  (eval_yul_loop n fns cond post body m =
     case eval_yul_expr n fns cond m of
       EvalAbrupt c m' => yul_pop_result (yul_abrupt c m')
     | EvalValues [v] m' =>
         if v = 0w then yul_normal (yul_pop_scope m')
         else
           let rb = yul_pop_result (eval_yul_block n fns body (yul_push_scope m')) in
             if rb.completion = YulBreak then
               yul_normal (yul_pop_scope rb.machine)
             else if rb.completion ≠ YulNormal ∧ rb.completion ≠ YulContinue then
               yul_pop_result rb
             else
               let rp = yul_pop_result
                          (eval_yul_block n fns post (yul_push_scope rb.machine)) in
                 if rp.completion ≠ YulNormal then yul_pop_result rp
                 else if n = 0 then
                   yul_abrupt YulOutOfFuel (yul_pop_scope rp.machine)
                 else eval_yul_loop (n - 1) fns cond post body rp.machine
     | EvalValues _ m' => yul_invalid "condition is not one value" (yul_pop_scope m')) ∧

  (* the case a switch runs: the first whose value matches, else the default;
   * a case value too long for the dialect is an error, not a skip *)
  (eval_yul_cases n fns v [] default m =
     yul_pop_result (eval_yul_block n fns default (yul_push_scope m))) ∧
  (eval_yul_cases n fns v ((lit, body) :: rest) default m =
     case yul_literal_value lit of
       NONE => yul_invalid "case value out of range" m
     | SOME w =>
         if w = v then
           yul_pop_result (eval_yul_block n fns body (yul_push_scope m))
         else eval_yul_cases n fns v rest default m) ∧

  (* a call: parameters in a scope of their own, results read out of it, then
   * leave, or falling off the end, returns them *)
  (invoke_yul n fns name args m =
     if n = 0 then EvalAbrupt YulOutOfFuel m
     else
       case FLOOKUP fns name of
         NONE => EvalAbrupt (YulInvalid "unknown function") m
       | SOME fd =>
           if LENGTH fd.function_params ≠ LENGTH args then
             EvalAbrupt (YulInvalid "bad call arity") m
           else
             let m1 = m with scopes :=
                        yul_bind_scope (FEMPTY : string |-> bytes32)
                          (ZIP (fd.function_params, args)) :: m.scopes in
             let r = eval_yul_block (n - 1) fns fd.function_body m1 in
             let m2 = r.machine with scopes := TL r.machine.scopes in
               if r.completion = YulNormal ∨ r.completion = YulLeave then
                 (case yul_lookup_names fd.function_results r.machine.scopes of
                    NONE => EvalAbrupt (YulInvalid "missing return binding") m2
                  | SOME vs => EvalValues vs m2)
               else EvalAbrupt r.completion m2)
Termination
  WF_REL_TAC `inv_image ($< LEX $<)
    (\x. case x of
           INL t => yul_measure_block t
         | INR (INL t) => yul_measure_stmt t
         | INR (INR (INL t)) => yul_measure_expr t
         | INR (INR (INR (INL t))) => yul_measure_args t
         | INR (INR (INR (INR (INL t)))) => yul_measure_loop t
         | INR (INR (INR (INR (INR (INL t))))) => yul_measure_cases t
         | INR (INR (INR (INR (INR (INR t))))) => yul_measure_invoke t)` >>
  rw[yul_measure_block_def, yul_measure_stmt_def, yul_measure_expr_def,
     yul_measure_args_def, yul_measure_loop_def, yul_measure_cases_def,
     yul_measure_invoke_def, listTheory.list_size_def,
     basicSizeTheory.pair_size_def, yul_expr_size_pos,
     yul_measure_loop_body_lt, yul_measure_loop_post_lt]
End


(* A program: the object's code, with its own functions collected, started in
 * a scope of its own.
 *)
Definition run_yul_def:
  run_yul n code m =
    eval_yul_block n (yul_env code) code
      (m with scopes := (FEMPTY : string |-> bytes32) :: m.scopes)
End

(* cv translation, so compiled Yul runs under cv_compute.  Termination of the
 * translated evaluator follows a scaled (fuel, size) order on the cv
 * encodings, strictly decreasing on every cv input.
 *)

(* PROBE: what breaks a translation that walks a list of finite maps? *)
fun dump_g (g : goal) =
  (print ("PROBE goal:\n" ^
          PP.pp_to_string 100 goalStack.std_pp_goal g ^ "\n");
   ALL_TAC g)

Definition probe_find_def:
  probe_find x (s : string |-> bytes32) = FLOOKUP s x
End

(* Recursion over a list whose element type is a finite map. *)
Definition probe_fmap_def:
  (probe_fmap ((s : string |-> bytes32) :: rest) = (1 : num) + probe_fmap rest) ∧
  (probe_fmap [] = 0)
End

(* FLOOKUP on a num-keyed map, inside recursion. *)
Definition probe_fl_num_def:
  (probe_fl_num ((s : num |-> word8) :: rest) =
     (case FLOOKUP s 0 of SOME v => (1 : num) | NONE => 0) + probe_fl_num rest) ∧
  (probe_fl_num [] = 0)
End

(* FLOOKUP on a string-keyed map, inside recursion, num result. *)
Definition probe_fl_str_def:
  (probe_fl_str x ((s : string |-> bytes32) :: rest) =
     (case FLOOKUP s x of SOME v => (1 : num) | NONE => 0) + probe_fl_str x rest) ∧
  (probe_fl_str x [] = 0)
End

(* An option result over a list of string-keyed maps, no FLOOKUP. *)
Definition probe_opt_def:
  (probe_opt ((s : string |-> bytes32) :: rest) =
     case probe_opt rest of NONE => SOME (0w : word8) | SOME v => SOME v) ∧
  (probe_opt [] = NONE)
End

(* The lookup itself. *)
Definition probe_lookup_def:
  (probe_lookup x ((s : string |-> bytes32) :: rest) =
     case FLOOKUP s x of SOME v => SOME v | NONE => probe_lookup x rest) ∧
  (probe_lookup x [] = NONE)
End

(* The lookup with its map type left to inference, and pinned. *)
Definition probe_poly_lookup_def:
  (probe_poly_lookup x [] = NONE) ∧
  (probe_poly_lookup x (scope :: rest) =
     case FLOOKUP scope x of SOME v => SOME v | NONE => probe_poly_lookup x rest)
End

Definition probe_mono_lookup_def:
  (probe_mono_lookup (x : string) [] = NONE) ∧
  (probe_mono_lookup (x : string) ((scope : string |-> bytes32) :: rest) =
     case FLOOKUP scope x of SOME v => SOME v | NONE => probe_mono_lookup x rest)
End

fun probe_try name f =
  (f (); print ("PROBE ok   " ^ name ^ "\n"))
  handle e => print ("PROBE FAIL " ^ name ^ " :: " ^ General.exnMessage e ^ "\n")

val _ = probe_try "lookup with the map type inferred"
  (fn () => cv_auto_trans probe_poly_lookup_def);
val _ = probe_try "lookup with the map type pinned"
  (fn () => cv_auto_trans probe_mono_lookup_def);
val _ = probe_try "non-recursive string fmap"
  (fn () => cv_auto_trans probe_find_def);
val _ = probe_try "recursive over list of string fmaps"
  (fn () => cv_auto_trans probe_fmap_def);
val _ = probe_try "recursive FLOOKUP num-keyed"
  (fn () => cv_auto_trans probe_fl_num_def);
val _ = probe_try "recursive FLOOKUP string-keyed, num result"
  (fn () => cv_auto_trans probe_fl_str_def);
val _ = probe_try "recursive option result, no FLOOKUP"
  (fn () => cv_auto_trans probe_opt_def);
val _ = probe_try "recursive lookup returning an option"
  (fn () => cv_auto_trans probe_lookup_def);

val () = cv_auto_trans yul_lookup_def;
val () = cv_auto_trans yul_lookup_names_def;
val () = cv_auto_trans yul_bind_scope_def;
val () = cv_auto_trans yul_bind_def;
val () = cv_auto_trans yul_assign_def;
val () = cv_auto_trans yul_literal_value_def;
val () = cv_auto_trans eval_yul_builtin_def;
val () = cv_auto_trans yul_env_def;

val () = cv_auto_trans_rec eval_yul_def (
  WF_REL_TAC `inv_image ($< LEX $<)
    (\x. case x of
           INL (n0, e0, s0, m0) => (cv$c2n n0, 2 * cv_size s0 + 2)
         | INR (INL (n0, e0, q0, m0)) => (cv$c2n n0, 2 * cv_size q0 + 2)
         | INR (INR (INL (n0, e0, x0, m0))) => (cv$c2n n0, 2 * cv_size x0 + 1)
         | INR (INR (INR (INL (n0, e0, x1, m0)))) =>
             (cv$c2n n0, 2 * cv_size x1)
         | INR (INR (INR (INR (INL (n0, e0, c0, p0, b0, m0))))) =>
             (cv$c2n n0,
              2 * (cv_size c0 + cv_size b0 + cv_size p0) + 1)
         | INR (INR (INR (INR (INR (INL (n0, e0, v0, cs0, d0, m0)))))) =>
             (cv$c2n n0, 2 * (cv_size cs0 + cv_size d0) + 3)
         | INR (INR (INR (INR (INR (INR (n0, e0, nm0, a0, m0)))))) =>
             (cv$c2n n0, 0))` >>
  cv_termination_tac >>
  rename1 `cv_snd (cv_snd x)` >> Cases_on `x` >> gvs[] >>
  rename1 `cv_snd y` >> Cases_on `y` >> gvs[]
);


val () = cv_auto_trans run_yul_def;
