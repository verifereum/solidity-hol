(* Core-to-HOL translator; see solidityTranslateLib.sig.
 *
 * Generation: symbolic execution of a procedure body over a map from ids to
 * shallow values. Temporaries, capture targets and copies only rename terms;
 * checked operations and calls become binds unless the path condition decides
 * their check; normal branches join before the remaining block. Branches
 * with abrupt source control flow retain their exits. A loop becomes a helper over the variables whose values on
 * entry it uses, called after the loop's first iteration; a boolean it only ever sets to one
 * constant at the top of its prelude (the elaborator's first-iteration flag)
 * is not a parameter. One loop per procedure, not nested.
 *
 * Proof: induction on the shallow definition, a case split along it, the
 * theorems of callees, helpers and the induction hypotheses at the calls it
 * makes, then rewriting the evaluator on the concrete body.
 *)
structure solidityTranslateLib :> solidityTranslateLib =
struct

open HolKernel boolLib bossLib
open solidityASTTheory solidityShallowTheory solidityEvaluatorTheory solidityEvaluatorPropsTheory
     solidityStateTheory
     solidityCoreTheory solidityCoreWfTheory solidityScalarTheory

val ERR = mk_HOL_ERR "solidityTranslateLib"
fun unsupported what = raise ERR "translate" ("unsupported: " ^ what)
(* A broken invariant of the translator itself *)
fun internal what = raise ERR "translate" what

(* Polymorphic constants *)
val returns_tm = prim_mk_const {Thy = "solidityShallow", Name = "Returns"}
val sol_bind_tm = prim_mk_const {Thy = "solidityShallow", Name = "sol_bind"}
val same_frames_tm = prim_mk_const {Thy = "solidityShallow", Name = "same_frames"}
val set_binding_tm = prim_mk_const {Thy = "solidityShallow", Name = "set_binding"}
val eval_block_tm = prim_mk_const {Thy = "solidityEvaluator", Name = "eval_block"}
val eval_loop_tm = prim_mk_const {Thy = "solidityEvaluator", Name = "eval_loop"}
val eval_stmt_tm = prim_mk_const {Thy = "solidityEvaluator", Name = "eval_stmt"}

(* Reading core terms *)

fun head_name tm =
  let val (f, _) = strip_comb tm in
    if is_const f then fst (dest_const f) else ""
  end

fun args_of tm = snd (strip_comb tm)

fun ast_id tm = numSyntax.int_of_term (rand tm)

fun dest_list tm = fst (listSyntax.dest_list tm)

datatype ty = Uint of int | Bool | Tup of ty list

fun dest_sol_type tm =
  case head_name tm of
    "UintT" => Uint (numSyntax.int_of_term (rand tm))
  | "BoolT" => Bool
  | _ => unsupported ("type " ^ term_to_string tm)

fun dest_value_type tm =
  case head_name tm of
    "SingleType" => dest_sol_type (rand tm)
  | "ProductType" =>
      Tup (map (fn t => dest_sol_type (rand t)) (dest_list (rand tm)))
  | _ => unsupported ("value type " ^ term_to_string tm)

fun hol_type (Uint _) = numSyntax.num
  | hol_type Bool = bool
  | hol_type (Tup ts) = pairSyntax.list_mk_prod (map hol_type ts)

fun sol_type_term (Uint n) = mk_comb (“UintT”, numSyntax.term_of_int n)
  | sol_type_term Bool = “BoolT”
  | sol_type_term (Tup _) = unsupported "tuple binding"

fun power_of_two n = numSyntax.mk_exp (numSyntax.term_of_int 2, numSyntax.term_of_int n)

fun range_facts (Uint n) v = [numSyntax.mk_less (v, power_of_two n)]
  | range_facts (Tup ts) v = List.concat
      (ListPair.map (fn (t, x) => range_facts t x)
         (ts, pairSyntax.strip_pair v))
  | range_facts _ _ = []

fun range_hyps decls vs =
  List.concat (ListPair.map (fn ((_, ty), v) => range_facts ty v) (decls, vs))

(* The core value of a shallow value *)
fun encode (Uint _) v = mk_comb (“uint_value”, v)
  | encode Bool v = mk_comb (“bool_value”, v)
  | encode (Tup _) _ = unsupported "tuple value"

fun mk_returns v = mk_icomb (returns_tm, v)

fun sol_result_ty ty = mk_thy_type {Thy = "solidityShallow", Tyop = "sol_result",
                                    Args = [ty]}

fun tuple_term [] = oneSyntax.one_tm
  | tuple_term vs = pairSyntax.list_mk_pair vs

fun tuple_type [] = oneSyntax.one_ty
  | tuple_type ts = pairSyntax.list_mk_prod ts

(* Fresh variables, distinct from every one made so far and from the
   variables the theorems bind themselves *)
val reserved = map (fn n => mk_var (n, bool)) ["m", "N", "st", "gas", "sc", "tg"]
val used = ref reserved
fun fresh name ty =
  let val v = prim_variant (!used) (mk_var (name, ty)) in used := v :: !used; v end

fun mk_call f [] = mk_comb (f, oneSyntax.one_tm)
  | mk_call f args = list_mk_comb (f, args)

(* \v. body, or \(x, y). body for a tuple pattern *)
fun mk_pattern_abs (p, body) =
  if is_var p then mk_abs (p, body)
  else if aconv p oneSyntax.one_tm then mk_abs (fresh "u" oneSyntax.one_ty, body)
  else pairSyntax.mk_pabs (p, body)

fun mk_bind (m, p, body) =
  list_mk_icomb (sol_bind_tm, [m, mk_pattern_abs (p, body)])

(* Symbolic states *)

type env = {vals : (int * (term * ty)) list, targets : (int * int) list}

fun lookup_val (env : env) x =
  case List.find (fn (y, _) => y = x) (#vals env) of
    SOME (_, v) => v
  | NONE => internal ("unbound id " ^ Int.toString x)

fun set_val (env : env) x v =
  {vals = (x, v) :: List.filter (fn (y, _) => y <> x) (#vals env),
   targets = #targets env}

fun bound (env : env) x = List.exists (fn (y, _) => y = x) (#vals env)

datatype exit = Normal | Break | Continue | Return of term | Next | Exit

datatype tree
  = Leaf of exit * env * term list
  | Bind of term * term * tree
  | Cond of term * tree * tree

fun graft k (Leaf (Normal, env, pc)) = k (env, pc)
  | graft k (l as Leaf _) = l
  | graft k (Bind (m, p, t)) = Bind (m, p, graft k t)
  | graft k (Cond (c, t1, t2)) = Cond (c, graft k t1, graft k t2)

fun map_exits f (Leaf (e, env, pc)) = Leaf (f e, env, pc)
  | map_exits f (Bind (m, p, t)) = Bind (m, p, map_exits f t)
  | map_exits f (Cond (c, t1, t2)) = Cond (c, map_exits f t1, map_exits f t2)

fun to_term leaf (Leaf (e, env, _)) = leaf (e, env)
  | to_term leaf (Bind (m, p, t)) = mk_bind (m, p, to_term leaf t)
  | to_term leaf (Cond (c, t1, t2)) =
      mk_cond (c, to_term leaf t1, to_term leaf t2)

(* Ground simplification of generated conditions *)
val tidy = rhs o concl o QCONV (SIMP_CONV (bool_ss ++ numSimps.REDUCE_ss) [])

fun decides pc goal =
  can (fn () => numLib.DECIDE (tidy (list_mk_imp (pc, goal)))) ()

(* Translation context *)

type callee = {shallow : term, returns : ty list}

type loop_info = {pre : term, cond : term, body : term,
                  params : (int * ty) list, consts : (int * term) list,
                  outs : (int * ty) list}

type context = {
  name : string,                          (* the procedure's shallow name *)
  names : (int * string) list,            (* source names of declarations *)
  callees : (int * callee) list,
  helper : (term * term * loop_info) option ref  (* variable, equation, loop *)
}

fun var_name (ctx : context) x =
  case List.find (fn (y, _) => y = x) (#names ctx) of
    SOME (_, s) => s
  | NONE => "t"

fun atom_value env tm =
  case head_name tm of
    "BoundAtom" => lookup_val env (ast_id (rand tm))
  | "ConstantAtom" =>
      let val s = rand tm in
        case head_name s of
          "IntegerValue" =>
            let val i = intSyntax.int_of_term (rand s) in
              if Arbint.< (i, Arbint.zero) then unsupported "negative constant"
              else (numSyntax.mk_numeral (Arbint.toNat i), Uint 256)
            end
        | "BoolValue" => (rand s, Bool)
        | _ => unsupported ("constant " ^ term_to_string s)
      end
  | _ => unsupported ("atom " ^ term_to_string tm)

datatype opres = Pure of term | Check of term * term * term

fun scalar_op (Uint n) checked oper vs =
  let
    fun bin f = case vs of [a, b] => f (a, b) | _ => internal "arity"
    val N = numSyntax.term_of_int n
    val B = power_of_two n
    fun need_checked () =
      if checked then () else unsupported "unchecked arithmetic"
  in
    case oper of
      "AddOp" => bin (fn (a, b) =>
        (need_checked ();
         Check (list_mk_comb (“uint_add”, [N, a, b]), numSyntax.mk_plus (a, b),
                numSyntax.mk_less (numSyntax.mk_plus (a, b), B))))
    | "SubtractOp" => bin (fn (a, b) =>
        (need_checked ();
         Check (list_mk_comb (“uint_sub”, [a, b]), numSyntax.mk_minus (a, b),
                numSyntax.mk_leq (b, a))))
    | "MultiplyOp" => bin (fn (a, b) =>
        (need_checked ();
         Check (list_mk_comb (“uint_mul”, [N, a, b]), numSyntax.mk_mult (a, b),
                numSyntax.mk_less (numSyntax.mk_mult (a, b), B))))
    | "DivideOp" => bin (fn (a, b) =>
        Check (list_mk_comb (“uint_div”, [a, b]), numSyntax.mk_div (a, b),
               mk_neg (mk_eq (b, numSyntax.zero_tm))))
    | "RemainderOp" => bin (fn (a, b) =>
        Check (list_mk_comb (“uint_mod”, [a, b]), numSyntax.mk_mod (a, b),
               mk_neg (mk_eq (b, numSyntax.zero_tm))))
    | "EqualOp" => bin (fn (a, b) => Pure (mk_eq (a, b)))
    | "LessThanOp" => bin (fn (a, b) => Pure (numSyntax.mk_less (a, b)))
    | _ => unsupported oper
  end
  | scalar_op Bool _ oper vs =
    (case (oper, vs) of
       ("BoolNotOp", [a]) => Pure (mk_neg a)
     | ("EqualOp", [a, b]) => Pure (mk_eq (a, b))
     | _ => unsupported oper)
  | scalar_op _ _ oper _ = unsupported oper

fun op_result_type oper ty =
  if oper = "EqualOp" orelse oper = "LessThanOp" then Bool else ty

(* A value bound by a bind: the pattern's variables, with range facts. *)
fun bind_pattern ctx x ty =
  case ty of
    Tup ts => tuple_term (map (fn t => fresh (var_name ctx x) (hol_type t)) ts)
  | _ => fresh (var_name ctx x) (hol_type ty)

(* Merging the branches of a pure if: a value per variable. *)
fun pure_normal (Leaf (Normal, _, _)) = true
  | pure_normal (Cond (_, t1, t2)) = pure_normal t1 andalso pure_normal t2
  | pure_normal _ = false

(* A checked operation or call may abort through its bind; its successful
   continuation is still normal. Source return/break/continue do not join. *)
fun normal_envs (Leaf (Normal, env, _)) = SOME [env]
  | normal_envs (Bind (_, _, tr)) = normal_envs tr
  | normal_envs (Cond (_, left, right)) =
      (case (normal_envs left, normal_envs right) of
         (SOME ls, SOME rs) => SOME (ls @ rs)
       | _ => NONE)
  | normal_envs _ = NONE

fun merged_value x (Leaf (_, env, _)) = fst (lookup_val env x)
  | merged_value x (Cond (c, t1, t2)) =
      let
        val a = merged_value x t1
        val b = merged_value x t2
      in
        if aconv a b then a
        else if type_of a = bool andalso aconv b c then mk_conj (c, a)
        else if type_of a = bool andalso aconv a c then mk_disj (c, b)
        else mk_cond (c, a, b)
      end
  | merged_value _ _ = raise ERR "merged_value" "not pure"

(* Statements of a loop, nested ones included *)
fun all_stmts tms = List.concat (map stmt_and_nested tms)
and stmt_and_nested s =
  s :: (case head_name s of
          "IfStmt" =>
            let val [_, ts, es] = args_of s in
              all_stmts (dest_list ts @ dest_list es)
            end
        | "WhileStmt" =>
            let val [p, _, b] = args_of s in
              all_stmts (dest_list p @ dest_list b)
            end
        | _ => [])

fun atoms_of s =
  find_terms (fn t => head_name t = "BoundAtom" andalso is_comb t) s

fun exec_stmt (ctx : context) (env : env) pc s =
  case (head_name s, args_of s) of
    ("DefineStmt", [x, vty, opn]) =>
      let val x = ast_id x in
        case (head_name opn, args_of opn) of
          ("ScalarOperation", [ty, mode, oper, atoms]) =>
            let
              val ty = dest_sol_type ty
              val oper = head_name oper
              val rty = op_result_type oper ty
              val vs = map (fst o atom_value env) (dest_list atoms)
            in
              case scalar_op ty (head_name mode = "CheckedArithmetic") oper vs of
                Pure t => Leaf (Normal, set_val env x (tidy t, rty), pc)
              | Check (m, plain, ok) =>
                  if decides pc ok then
                    Leaf (Normal, set_val env x (tidy plain, rty), pc)
                  else
                    let val v = bind_pattern ctx x rty in
                      Bind (m, v, Leaf (Normal, set_val env x (v, rty),
                                        range_facts rty v @ pc))
                    end
            end
        | ("ConvertOperation", [ty, a]) =>
            let
              val ty = dest_sol_type ty
              val (v, vty) = atom_value env a
            in
              if vty = ty orelse head_name a = "ConstantAtom" then
                Leaf (Normal, set_val env x (v, ty), pc)
              else unsupported "conversion between types"
            end
        | ("TupleOperation", [atoms]) =>
            let val vs = map (atom_value env) (dest_list atoms) in
              Leaf (Normal, set_val env x (tuple_term (map fst vs),
                                           Tup (map snd vs)), pc)
            end
        | ("TupleComponentOperation", [n, a]) =>
            (case atom_value env a of
               (v, Tup ts) =>
                 let val i = numSyntax.int_of_term n in
                   Leaf (Normal, set_val env x
                     (List.nth (pairSyntax.strip_pair v, i), List.nth (ts, i)),
                         pc)
                 end
             | _ => internal "component of a non-tuple")
        | ("InternalCallOperation", [f, atoms]) =>
            let
              val {shallow, returns, ...} =
                case List.find (fn (y, _) => y = ast_id f) (#callees ctx) of
                  SOME (_, c) => c
                | NONE => unsupported ("call of " ^ term_to_string f)
              val vs = map (fst o atom_value env) (dest_list atoms)
              val rty = case returns of [t] => t | ts => Tup ts
              val p = bind_pattern ctx x rty
            in
              Bind (mk_call shallow vs, p,
                    Leaf (Normal, set_val env x (p, rty), range_facts rty p @ pc))
            end
        | _ => unsupported ("operation " ^ head_name opn)
      end
  | ("CaptureBindingStmt", [t, x]) =>
      Leaf (Normal, {vals = #vals env,
                     targets = (ast_id t, ast_id x) :: #targets env}, pc)
  | ("WriteScalarStmt", [t, ty, a]) =>
      let
        val x = case List.find (fn (u, _) => u = ast_id t) (#targets env) of
                  SOME (_, x) => x
                | NONE => internal "write without capture"
      in
        Leaf (Normal, set_val env x (fst (atom_value env a), dest_sol_type ty), pc)
      end
  | ("IfStmt", [c, ts, es]) =>
      let
        val c = tidy (fst (atom_value env c))
        val ts = dest_list ts
        val es = dest_list es
      in
        if aconv c T orelse decides pc c then exec_block ctx env pc ts
        else if aconv c F orelse decides pc (mk_neg c) then
          exec_block ctx env pc es
        else
          let
            val t1 = exec_block ctx env (c :: pc) ts
            val t2 = exec_block ctx env (mk_neg c :: pc) es
            val tr = Cond (c, t1, t2)
          in
            case normal_envs tr of
              NONE => tr
            | SOME leaves =>
                let
                  (* A loop helper may omit an overwritten input, so bindings
                     established by every successful arm must join too. *)
                  val added = List.filter
                    (fn (x, _) => not (bound env x) andalso
                                  List.all (fn e => bound e x) leaves)
                    (#vals (hd leaves))
                  val bindings = #vals env @ added
                in
                  if pure_normal tr then
                    Leaf (Normal,
                          {vals = map (fn (x, (_, ty)) =>
                                   (x, (tidy (merged_value x tr), ty))) bindings,
                           targets = #targets env}, pc)
                  else let
                    val changed = List.filter
                      (fn (x, (v, _)) => not (bound env x) orelse List.exists
                        (fn e => not (aconv v (fst (lookup_val e x)))) leaves)
                      bindings
                    val outs = map (fn (x, (_, ty)) => (x, ty)) changed
                    val vs = map (fn (x, ty) => fresh (var_name ctx x) (hol_type ty)) outs
                    fun joined (Normal, e) = mk_returns (tuple_term
                          (map (fn (x, _) => fst (lookup_val e x)) outs))
                      | joined _ = raise ERR "exec_stmt" "non-normal join"
                    val env' = foldl (fn (((x, ty), v), e) => set_val e x (v, ty))
                                     env (ListPair.zip (outs, vs))
                  in
                    Bind (to_term joined tr, tuple_term vs,
                          Leaf (Normal, env', range_hyps outs vs @ pc))
                  end
                end
          end
      end
  | ("WhileStmt", [pre, c, body]) => exec_loop ctx env pc (pre, c, body)
  | ("ReturnStmt", [atoms]) =>
      Leaf (Return (tuple_term (map (fst o atom_value env) (dest_list atoms))),
            env, pc)
  | ("BreakStmt", []) => Leaf (Break, env, pc)
  | ("ContinueStmt", []) => Leaf (Continue, env, pc)
  | _ => unsupported ("statement " ^ head_name s)

and exec_block ctx env pc [] = Leaf (Normal, env, pc)
  | exec_block ctx env pc (s :: ss) =
      graft (fn (e, p) => exec_block ctx e p ss) (exec_stmt ctx env pc s)

and exec_loop (ctx : context) (env : env) pc (pre, c, body) =
  let
    val pre_s = dest_list pre
    val body_s = dest_list body
    val stmts = all_stmts (pre_s @ body_s)
    val () = if List.exists (fn s => head_name s = "WhileStmt") stmts
             then unsupported "nested loop" else ()
    val captures =
      List.mapPartial
        (fn s => if head_name s = "CaptureBindingStmt"
                 then let val [t, x] = args_of s in SOME (ast_id t, ast_id x) end
                 else NONE) stmts @ #targets env
    fun target t = case List.find (fn (u, _) => u = t) captures of
                     SOME (_, x) => x
                   | NONE => internal "write without capture"
    val writes =
      List.mapPartial
        (fn s => if head_name s = "WriteScalarStmt"
                 then let val [t, _, a] = args_of s in SOME (target (ast_id t), a) end
                 else NONE) stmts
    val written = Lib.mk_set (List.filter (bound env) (map fst writes))
    val read = Lib.mk_set (List.filter (bound env)
                 (map (ast_id o rand) (List.concat (map atoms_of [pre, c, body]))))
    (* boolean variables set to one constant at the top of the prelude, and
       nowhere else to anything else *)
    val top_consts =
      List.mapPartial
        (fn s => if head_name s = "WriteScalarStmt" then
                   let
                     val [t, _, a] = args_of s
                     val x = target (ast_id t)
                   in
                     if head_name a = "ConstantAtom" andalso bound env x andalso
                        snd (lookup_val env x) = Bool
                     then SOME (x, fst (atom_value env a))
                     else NONE
                   end
                 else NONE) pre_s
    val consts =
      List.filter
        (fn (x, k) => List.all (fn (y, a) => y <> x orelse
                                  (head_name a = "ConstantAtom" andalso
                                   aconv (fst (atom_value env a)) k)) writes)
        top_consts
    val is_const = fn x => List.exists (fn (y, _) => y = x) consts
    val sorted = Listsort.sort Int.compare
    val outs = sorted (List.filter (not o is_const) written)
    val otys = map (fn x => (x, snd (lookup_val env x))) outs
    val out_ty = tuple_type (map (hol_type o snd) otys)
    fun with_consts e = foldl (fn ((x, k), e) => set_val e x (k, Bool)) e consts
    fun iteration env pc =
      graft (fn (e1, p1) =>
        let
          val cv = tidy (fst (atom_value e1 c))
          fun exits Normal = Next
            | exits Continue = Next
            | exits Break = Exit
            | exits (Return _) = unsupported "return inside a loop"
            | exits e = e
          fun run p = map_exits exits (exec_block ctx e1 p body_s)
        in
          if aconv cv F then Leaf (Exit, e1, p1)
          else if aconv cv T then run p1
          else Cond (cv, run (cv :: p1), Leaf (Exit, e1, mk_neg cv :: p1))
        end)
        (map_exits (fn Normal => Normal
                     | _ => unsupported "control flow out of a loop prelude")
           (exec_block ctx env pc pre_s))
    fun leaf hvar ptys (Next, e) =
          (List.app (fn (x, k) => if aconv (fst (lookup_val e x)) k then ()
                                  else unsupported "loop flag not constant")
                    consts;
           mk_call hvar (map (fn (x, _) => fst (lookup_val e x)) ptys))
      | leaf _ _ (Exit, e) =
          mk_returns (tuple_term (map (fn x => fst (lookup_val e x)) outs))
      | leaf _ _ _ = raise ERR "exec_loop" "unexpected exit"
    (* the helper over the given parameters, with its own variable names *)
    fun helper ptys =
      let
        val hvar = mk_var (#name ctx ^ "_loop",
                           foldr (op -->) (sol_result_ty out_ty)
                             (if null ptys then [oneSyntax.one_ty]
                              else map (hol_type o snd) ptys))
        val outer_used = !used
        val () = used := reserved
        val pvars = map (fn (x, ty) => fresh (var_name ctx x) (hol_type ty)) ptys
        val henv = with_consts
                     {vals = ListPair.map (fn ((x, ty), v) => (x, (v, ty))) (ptys, pvars),
                      targets = #targets env}
        val rhs = to_term (leaf hvar ptys) (iteration henv (range_hyps ptys pvars))
      in
        used := outer_used;
        (hvar, pvars, mk_eq (mk_call hvar pvars, rhs))
      end
    (* a loop reached along several paths has one helper *)
    val (hvar, ptys) =
      case !(#helper ctx) of
        SOME (hvar, _, i : loop_info) =>
          if aconv (#pre i) pre andalso aconv (#cond i) c andalso aconv (#body i) body
          then (hvar, #params i) else unsupported "more than one loop"
      | NONE =>
          let
            (* the variables it reads or writes, less those whose value on
               entry it never uses (written before read) *)
            val all = map (fn x => (x, snd (lookup_val env x)))
                          (sorted (List.filter (not o is_const) (Lib.union read written)))
            val (_, pvars, eqn) = helper all
            val ptys = map fst (List.filter (fn (_, v) => free_in v (rhs eqn))
                                            (ListPair.zip (all, pvars)))
            val (hvar, _, eqn) = helper ptys
          in
            #helper ctx := SOME (hvar, eqn, {pre = pre, cond = c, body = body,
                                             params = ptys, consts = consts,
                                             outs = otys});
            (hvar, ptys)
          end
    (* the loop here: its first iteration, then the helper *)
    val m = to_term (leaf hvar ptys) (iteration env pc)
    val pat = tuple_term (map (fn (x, ty) => fresh (var_name ctx x) (hol_type ty)) otys)
    val outvs = pairSyntax.strip_pair pat
    val env' = with_consts
                 (foldl (fn (((x, ty), v), e) => set_val e x (v, ty)) env
                        (ListPair.zip (otys, outvs)))
    val pc' = range_hyps otys outvs
  in
    Bind (m, pat, Leaf (Normal, env', pc' @ pc))
  end

(* Procedures *)

fun default_value (Uint _) = numSyntax.zero_tm
  | default_value Bool = F
  | default_value _ = unsupported "tuple return"

fun dest_decl p =
  let val (x, t) = pairSyntax.dest_pair p in (ast_id x, dest_sol_type t) end

(* core_procedure id params returns body *)
fun dest_procedure tm =
  case args_of tm of
    [_, ps, rs, body] => (map dest_decl (dest_list ps), map dest_decl (dest_list rs),
                          dest_list body)
  | _ => unsupported ("procedure " ^ term_to_string tm)

(* sol_bind m (λx. Returns x) is m *)
fun drop_returns tm =
  if is_comb tm then
    let
      val tm' = mk_comb (drop_returns (rator tm), drop_returns (rand tm))
    in
      case strip_comb tm' of
        (c, [m, f]) =>
          if same_const c sol_bind_tm andalso is_abs f andalso
             aconv (snd (dest_abs f)) (mk_returns (bvar f))
          then m else tm'
      | _ => tm'
    end
  else if is_abs tm then
    let val (v, b) = dest_abs tm in mk_abs (v, drop_returns b) end
  else tm

fun procedure_equation ctx fvar (ps, rs, body) =
  let
    val pvars = map (fn (x, ty) => fresh (var_name ctx x) (hol_type ty)) ps
    val env = {vals = ListPair.map (fn ((x, ty), v) => (x, (v, ty))) (ps, pvars) @
                      map (fn (x, ty) => (x, (default_value ty, ty))) rs,
               targets = []}
    fun leaf (Return t, _) = mk_returns t
      | leaf (Normal, e) =
          mk_returns (tuple_term (map (fn (x, _) => fst (lookup_val e x)) rs))
      | leaf _ = unsupported "break or continue outside a loop"
    val rhs = to_term leaf (exec_block ctx env (range_hyps ps pvars) body)
  in
    (pvars, mk_eq (mk_call fvar pvars, drop_returns rhs))
  end

(* Statements *)

val st_var = mk_var ("st", “:source_state”)

fun binding ty v =
  “<| binding_type := SingleType ^(sol_type_term ty); binding_value := ^(encode ty v) |>”

fun has_binding (x, ty, v) =
  “lookup_binding (AstId ^(numSyntax.term_of_int x)) ^st_var.scopes = SOME ^(binding ty v)”

fun value_list tys vs =
  listSyntax.mk_list (ListPair.map (fn (ty, v) => encode ty v) (tys, vs),
                      type_of (encode Bool T))

(* Variables for results, apart from the variables of t *)
fun result_vars ctx t decls =
  let
    fun next ((x, ty), vs) =
      prim_variant (vs @ reserved @ free_vars t) (mk_var (var_name ctx x, hol_type ty)) :: vs
  in rev (foldl next [] decls) end

(* ∀rs. call = Returns rs ⇒ ranges, if there are any *)
fun result_ranges ctx call decls =
  let
    val rvs = result_vars ctx call decls
    val rs = range_hyps decls rvs
  in
    if null rs then []
    else [list_mk_forall (rvs, mk_imp (mk_eq (call, mk_returns (tuple_term rvs)),
                                       list_mk_conj rs))]
  end

fun hyps_imp [] t = t
  | hyps_imp hs t = mk_imp (list_mk_conj hs, t)

fun procedure_goal ctx env id fconst pvars ps rs =
  let
    val call = mk_call fconst pvars
    val rvs = result_vars ctx call rs
    val enc = mk_pattern_abs (tuple_term rvs, value_list (map snd rs) rvs)
    val args = value_list (map snd ps) pvars
    val main =
      “∃N. ∀m ^st_var gas. N ≤ m ⇒
         invoke_source m ^env (AstId ^(numSyntax.term_of_int id)) ^args ^st_var gas =
         <| completion := result_completion ^enc ^call; state := ^st_var;
            unused_gas_evidence := gas |>”
  in
    list_mk_forall (pvars, hyps_imp (range_hyps ps pvars)
                             (list_mk_conj (result_ranges ctx call rs @ [main])))
  end

fun loop_goal ctx env hconst pvars ({pre, cond, body, params, consts, outs} : loop_info) =
  let
    val call = mk_call hconst pvars
    val ovs = result_vars ctx call outs
    (* results the loop writes before it reads them are bound to something *)
    val fresh_outs = List.filter (fn (x, _) => not (exists (fn (y, _) => y = x) params)) outs
    val lookups =
      ListPair.map (fn ((x, ty), v) => has_binding (x, ty, v)) (params, pvars) @
      ListPair.map (fn ((x, ty), v) => mk_exists (v, has_binding (x, ty, v)))
                   (fresh_outs, result_vars ctx call fresh_outs) @
      map (fn (x, k) => has_binding (x, Bool, k)) consts
    val writes =
      ListPair.map (fn ((x, ty), v) => pairSyntax.mk_pair
                      (“AstId ^(numSyntax.term_of_int x)”, encode ty v)) (outs, ovs) @
      map (fn (x, k) => pairSyntax.mk_pair
             (“AstId ^(numSyntax.term_of_int x)”, encode Bool k)) consts
    val writes = listSyntax.mk_list (writes, pairSyntax.mk_prod (“:ast_id”, type_of (encode Bool T)))
    val post = list_mk_forall (ovs,
                 mk_imp (mk_eq (call, mk_returns (tuple_term ovs)),
                         “sc = set_bindings ^writes ^st_var.scopes”))
    val main =
      “∃N. ∀m ^st_var gas. N ≤ m ∧ ^(list_mk_conj lookups) ⇒
         ∃sc tg.
           eval_loop m ^env ^pre ^cond ^body ^st_var gas =
           <| completion := loop_completion ^call;
              state := ^st_var with <| scopes := sc; targets := tg |>;
              unused_gas_evidence := gas |> ∧ ^post”
  in
    list_mk_forall (pvars, hyps_imp (range_hyps params pvars)
                             (list_mk_conj (result_ranges ctx call outs @ [main])))
  end

(* Proofs *)

val op_defs = [uint_add_def, uint_sub_def, uint_mul_def, uint_div_def, uint_mod_def]

val eval_simps =
  [ast_key_def, entry_scope_def, bind_parameters_def, bind_defaults_def,
   default_scalar_def, default_elementary_def, single_binding_def,
   enter_procedure_def, eval_operation_def, eval_pure_operation_def, eval_atom_def, eval_atoms_def,
   lookup_binding_def, finite_mapTheory.FLOOKUP_UPDATE,
   finite_mapTheory.FLOOKUP_FUNION, scalar_values_def,
   conversion_source_type_def, scalar_outcome_value_def, loop_after_body_def,
   uint_add_op, uint_sub_op, uint_mul_op, uint_div_op, uint_mod_op,
   uint_less_op, uint_equal_op, bool_equal_op, bool_not_op, uint_copy_conversion,
   bool_copy_conversion, define_binding_def, bind_local_def, write_target_def,
   set_target_def, update_binding_set_binding, set_binding_def,
   lookup_set_binding, set_bindings_def, branch_of_def, push_scope_def,
   pop_scopes_def, normal_result_def, abrupt_result_def, pack_results_def,
   procedure_completion_def, read_returns_def, restore_caller_def,
   result_completion_def, result_outcome_def, loop_completion_def,
   uint_value_def, bool_value_def, valid_int_width_def, simple_stmt_def,
   source_state_component_equality, eval_block_cons, result_literal_eqs, listTheory.oEL_def,
   uint_div_range, uint_mod_range, uint_mod_divisor_range] @
  List.filter (fn th => let val (h, args) = strip_comb (lhs (concl (SPEC_ALL th))) in
                          same_const h eval_stmt_tm orelse
                          same_const h eval_block_tm andalso listSyntax.is_nil (el 3 args)
                        end) (CONJUNCTS eval_block_def) @ op_defs

fun is_call heads t =
  let val (h, args) = strip_comb t in
    is_const h andalso exists (same_const h) heads andalso
    length args = length (fst (strip_fun (type_of h)))
  end handle HOL_ERR _ => false

(* Instances of facts ∀xs. ... f xs ... at the calls of f in the goal. A
   variable the call does not fix, such as an earlier call's result in an
   induction hypothesis, is fixed by matching the antecedents against the
   assumptions. *)
fun fact_instances heads facts (asl, w) =
  let
    val calls = op_mk_set aconv (List.concat (map (find_terms (is_call heads)) (w :: asl)))
    fun fixed s v = exists (fn {redex, ...} => aconv redex v) s
    fun fill rest (c, s) =
      let
        val c' = subst s c
        fun matches a =
          let val (s', _) = match_term c' a in
            if List.all (fn {redex, ...} => exists (aconv redex) rest) s'
            then SOME s' else NONE
          end handle HOL_ERR _ => NONE
      in
        if exists (fn v => free_in v c') rest
        then case List.mapPartial matches asl of s' :: _ => s @ s' | [] => s
        else s
      end
    fun inst th =
      let
        val (vs, body) = strip_forall (concl th)
        val pat = find_term (is_call heads) body
        fun at c =
          let val (s, _) = match_term pat c in
            if List.all (fn {redex, ...} => exists (aconv redex) vs) s
            then
              let
                val th1 = INST s (SPEC_ALL th)
                val rest = List.filter (not o fixed s) vs
                val ants = List.concat (map strip_conj (fst (strip_imp (concl th1))))
              in SOME (INST (foldl (fill rest) [] ants) th1) end
            else NONE
          end handle HOL_ERR _ => NONE
      in List.mapPartial at calls end
      handle HOL_ERR _ => []
  in List.concat (map inst facts) end

(* Use the facts at their instances whose antecedents hold here, until no
   new instance holds: a call's arguments can be in range only by the facts
   about an earlier call *)
fun use_facts_tac heads facts =
  let
    fun discharge asl th =
      let val th1 = REWRITE_RULE [AND_IMP_INTRO] th in
        (* a callee without range hypotheses (bool or no arguments) *)
        if not (is_imp (concl th1)) then SOME (th, th1)
        else
          let val (a, _) = dest_imp (concl th1)
              (* gvs, not asm_simp_tac: the assumptions' 2 ** n must be
                 evaluated like the goal's for arithmetic to relate them *)
              val pf = TAC_PROOF ((asl, a), gvs (sol_bind_def :: op_defs))
          in SOME (th, MP th1 pf) end
      end
      handle HOL_ERR _ => NONE
    fun use used (g as (asl, _)) =
      let
        val new = List.filter (fn th => not (exists (aconv (concl th)) used))
                              (fact_instances heads facts g)
        val ths = List.mapPartial (discharge asl) new
      in
        if null ths then ALL_TAC g
        else (MAP_EVERY (strip_assume_tac o snd) ths >>
              use (map (concl o fst) ths @ used)) g
      end
  in use [] end

fun uncurry_tac (g as (_, w)) =
  let val t = find_term (fn t => is_comb t andalso pairSyntax.is_uncurry (rator t)
                                 andalso is_var (rand t)) w
  in (FULL_STRUCT_CASES_TAC (ISPEC (rand t) pairTheory.pair_CASES) >>
      simp_tac (srw_ss()) []) g end

(* Joined continuations can leave a tuple pattern application in a case
   equation rather than in the conclusion. Expose just those opaque product
   arguments; each split removes one variable-argument UNCURRY application. *)
fun expose_tuples_tac (g as (asl, w)) =
  let
    fun in_formula formula =
      Lib.total (find_term (fn t =>
        is_comb t andalso pairSyntax.is_uncurry (rator t) andalso
        is_var (rand t) andalso free_in (rand t) formula)) formula
    val pending = List.mapPartial in_formula (w :: asl)
  in
    case pending of
      [] => ALL_TAC g
    | t :: _ =>
        (FULL_STRUCT_CASES_TAC (ISPEC (rand t) pairTheory.pair_CASES) >>
         gvs [sol_bind_def] >> expose_tuples_tac) g
  end

(* gvs turns f c = Returns v, for a call f c with constant arguments, into
   Returns v = f c, which no longer rewrites the call; turn such facts back
   and rewrite with them *)
fun flipped a =
  is_eq a andalso null (free_vars (rhs a)) andalso not (null (free_vars (lhs a)))
  andalso mem (head_name (lhs a)) ["Returns", "Reverts", "Panics"]

fun unflip_tac simps (g as (asl, _)) =
  (if exists flipped asl
   then rpt (first_x_assum (fn th =>
               if flipped (concl th) then assume_tac (GSYM th) else NO_TAC)) >>
        asm_simp_tac (srw_ss()) simps
   else ALL_TAC) g

fun gvs_tac simps = gvs simps >> unflip_tac simps

(* A case split along the shallow definition's control flow. The induction
   hypotheses are about the function's own parameters, so they are also
   used before gvs eliminates a parameter together with the branch
   condition that discharges them. *)
fun split_tac heads ihs facts =
  simp_tac (srw_ss()) [sol_bind_def] >>
  rpt (BasicProvers.TOP_CASE_TAC ORELSE IF_CASES_TAC ORELSE uncurry_tac) >>
  use_facts_tac heads ihs >>
  gvs_tac (AllCaseEqs() :: op_defs) >>
  expose_tuples_tac >>
  use_facts_tac heads (ihs @ facts)

fun ranges_tac (g as (_, w)) =
  (if is_conj w then
     conj_tac >- (rpt strip_tac >> gvs [] >> res_tac >> gvs [uint_div_range, uint_mod_range])
   else ALL_TAC) g

(* Fuel: the sum of the fuel bounds of the facts in use, and some to spare *)
fun fuel_tac (asl, w) =
  let
    fun fuel a =
      let val (vs, b) = strip_forall a
          val (l, _) = dest_imp b
          val (n, m) = numSyntax.dest_leq (hd (strip_conj l))
      in if is_var n andalso exists (aconv m) vs then SOME n else NONE end
      handle HOL_ERR _ => NONE
    val ns = op_mk_set aconv (List.mapPartial fuel asl)
    val wit = foldl (fn (n, acc) => numSyntax.mk_plus (acc, n))
                    (numSyntax.term_of_int 3) ns
  in exists_tac wit (asl, w) end

fun is_eval_loop t =
  is_comb t andalso same_const (fst (strip_comb t)) eval_loop_tm andalso
  length (snd (strip_comb t)) = 7

(* Replace a loop by its theorem's result *)
fun loop_step simps (g as (asl, w)) =
  case Lib.total (find_term is_eval_loop) w of
    NONE => ALL_TAC g
  | SOME lp =>
      let
        val [m, _, pre, _, _, st, gas] = snd (strip_comb lp)
        fun matches a =
          let val (vs, b) = strip_forall a
              val (_, c) = dest_imp b
          in length vs = 3 andalso
             can (find_term (fn t => is_eval_loop t andalso
                                     aconv (el 3 (snd (strip_comb t))) pre)) c
          end handle HOL_ERR _ => false
        val a = Lib.first matches asl
      in
        (mp_tac (SPECL [m, st, gas] (ASSUME a)) >>
         impl_tac >- asm_simp_tac (srw_ss() ++ numSimps.ARITH_ss) simps >>
         disch_then strip_assume_tac >>
         asm_simp_tac (srw_ss()) []) g
      end

fun base_scopes t =
  case strip_comb t of
    (h, [_, _, sc]) => if same_const h set_binding_tm then base_scopes sc else t
  | _ => t

fun frames_tac (g as (_, w)) =
  (if (same_const (fst (strip_comb w)) same_frames_tm handle HOL_ERR _ => false)
   then simp[] >> rpt (irule same_frames_set_binding) >> simp[same_frames_refl]
   else rw[lookup_set_binding, ast_key_def] >> gvs[]) g

(* scopes = set_bindings ... by extensionality *)
fun ext_tac (g as (_, w)) =
  (irule same_frames_ext >> conj_tac >- frames_tac >>
   exists_tac (base_scopes (rhs w)) >> conj_tac >> frames_tac) g

fun loop_case_tac simps =
  ranges_tac >> fuel_tac >> rpt strip_tac >> once_rewrite_tac [eval_loop_unfold] >>
  gvs_tac simps >> loop_step simps >>
  simp[source_state_component_equality] >> rpt strip_tac >>
  rpt (first_x_assum drule >> disch_then SUBST1_TAC) >> ext_tac

fun peel_tac simps (g as (_, w)) =
  (if can (find_term is_eval_loop) w
   then once_rewrite_tac [eval_loop_unfold] >> gvs_tac simps >> loop_step simps
   else ALL_TAC) g

fun procedure_case_tac simps =
  ranges_tac >> fuel_tac >> rpt strip_tac >> once_rewrite_tac [invoke_source_unfold] >>
  gvs_tac simps >> peel_tac simps >> rpt (first_x_assum drule >> strip_tac) >>
  gvs_tac simps >>
  (* what is left: branches, and the result of a call in tail position *)
  rpt ((IF_CASES_TAC >> gvs_tac simps) ORELSE
       (BasicProvers.TOP_CASE_TAC >> gvs_tac (AllCaseEqs() :: simps)))

fun intro_tac (g as (_, w)) = (if is_imp w then strip_tac else ALL_TAC) g

(* Induction along the definition when it is recursive *)
fun along_tac def ind heads facts =
  case ind of
    SOME ind =>
      ho_match_mp_tac ind >> rpt gen_tac >> disch_then (fn ih =>
        intro_tac >> once_rewrite_tac [def] >> split_tac heads (CONJUNCTS ih) facts)
  | NONE => rpt gen_tac >> intro_tac >> once_rewrite_tac [def] >> split_tac heads [] facts

(* Definitions *)

fun define name eqn termination =
  let
    val def = case termination of
                SOME tac => fst (TotalDefn.tDefine name [ANTIQUOTE eqn] tac)
              | NONE => TotalDefn.Define [ANTIQUOTE eqn]
    val c = fst (strip_comb (lhs (snd (strip_forall (hd (strip_conj (concl def)))))))
    val ind = Lib.total (DB.fetch "-") (name ^ "_ind")
  in (def, c, ind) end

(* The translator *)

type translated = {callee : callee, thm : thm}
val translated = ref ([] : (int * translated) list)

fun translate {env, lookup, name, id, names, termination, loop} =
  let
    val () = used := reserved
    val lookup_th = lookup “lookup_procedure ^env (AstId ^(numSyntax.term_of_int id))”
    val proc = rand (rhs (concl lookup_th))
    val (ps, rs, body) = dest_procedure proc
    val fvar = mk_var (name, foldr (op -->)
                                   (sol_result_ty (tuple_type (map (hol_type o snd) rs)))
                                   (if null ps then [oneSyntax.one_ty]
                                    else map (hol_type o snd) ps))
    val ctx = {name = name, names = names,
               callees = (id, {shallow = fvar, returns = map snd rs}) ::
                         map (fn (i, t) => (i, #callee t)) (!translated),
               helper = ref NONE} : context
    val (pvars, eqn) = procedure_equation ctx fvar (ps, rs, body)
    val simps = lookup_th :: eval_simps
    val callee_heads = map (#shallow o #callee o snd) (!translated)
    val callee_thms = map (#thm o snd) (!translated)
    val helpers =
      case (!(#helper ctx), loop) of
        (NONE, _) => []
      | (SOME (hvar, heqn, info), SOME tac) =>
          let
            val (def, c, ind) = define (fst (dest_var hvar)) heqn (SOME tac)
            val hpvars = snd (strip_comb (lhs heqn))
            val goal = loop_goal ctx env c hpvars info
            val th = prove (goal, along_tac def ind (c :: callee_heads) callee_thms >>
                                  loop_case_tac simps)
            val _ = save_thm (fst (dest_var hvar) ^ "_correct", th)
          in [(hvar, c, th)] end
      (* not Define: under holbuild a failed termination proof ends the
         theory build even when handled *)
      | (SOME _, NONE) => unsupported "loop without a termination tactic"
    val s = map (fn (v, c, _) => v |-> c) helpers
    val (def, c, ind) = define name (Term.subst s eqn) termination
    val goal = procedure_goal ctx env id c pvars ps rs
    val heads = c :: map #2 helpers @ callee_heads
    val facts = map #3 helpers @ callee_thms
    val th = prove (goal, along_tac def ind heads facts >> procedure_case_tac simps)
    val th = save_thm (name ^ "_correct", th)
  in
    translated := (id, {callee = {shallow = c, returns = map snd rs},
                        thm = th}) :: !translated;
    th
  end

(* Units *)

datatype outcome = Proved of thm | Unsupported of string | Failed of string
type result = {name : string, outcome : outcome, seconds : real}

fun callees proc =
  map (ast_id o hd o args_of)
      (find_terms (fn t => head_name t = "InternalCallOperation" andalso
                           length (args_of t) = 2) proc)

(* Callees before callers; a cycle other than a self-call is left in program
   order, and its first call of an untranslated procedure is unsupported *)
fun call_order ids calls =
  let
    fun visit (x, (seen, out)) =
      if mem x seen then (seen, out)
      else
        let val (seen, out) =
              foldl visit (x :: seen, out)
                    (List.filter (fn y => y <> x andalso mem y ids) (calls x))
        in (seen, x :: out) end
  in rev (snd (foldl visit ([], []) ids)) end

fun unsupported_message (HOL_ERR e) =
      let val m = message_of e in
        if String.isPrefix "unsupported: " m then SOME m else NONE
      end
  | unsupported_message _ = NONE

fun translate_unit {prefix, unit_def, program_def, termination, loops} =
  let
    val () = translated := []
    val env_var = mk_var (prefix ^ "env", type_of “core_program_environment p”)
    val env_def = new_definition (prefix ^ "env_def",
      mk_eq (env_var, “core_program_environment ^(lhs (concl program_def))”))
    val env = lhs (concl env_def)
    val lookup = REWRITE_CONV [lookup_procedure_def, env_def,
                               core_program_environment_def, program_def]
                 THENC EVAL
    val unit = lhs (concl unit_def)
    fun eval tm = rhs (concl ((REWRITE_CONV [unit_def] THENC EVAL) tm))
    val fns = dest_list (eval “FLAT (MAP (λc. c.contract_functions)
                                         ^unit.unit_contracts)”)
    fun info f =
      let
        val id = numSyntax.int_of_term (eval “(^f).fn_info.node_id”)
        val name = stringSyntax.fromHOLstring (eval “(^f).fn_name”)
        val vars = HOLset.listItems (HOLset.addList (empty_tmset,
                     find_terms (fn t => type_of t = “:src_variable”) f))
        fun named v =
          SOME (numSyntax.int_of_term (eval “(^v).var_info.node_id”),
                stringSyntax.fromHOLstring (eval “(^v).var_name”))
          handle HOL_ERR _ => NONE
      in
        (id, {name = name,
              names = List.filter (fn (_, s) => s <> "") (List.mapPartial named vars)})
      end
    val infos = map info fns
    val ids = map fst infos
    (* termination and loops are keyed by name *)
    fun overloaded name =
      length (List.filter (fn (_, i) => #name i = name) infos) > 1
    fun calls id =
      callees (rhs (concl (lookup “lookup_procedure ^env (AstId ^(numSyntax.term_of_int id))”)))
    fun run id =
      let
        val {name, names} = Lib.assoc id infos
        val timer = Timer.startRealTimer ()
        val outcome =
          if overloaded name then
            Unsupported "unsupported: overloaded function"
          else
            Proved (translate {env = env, lookup = lookup, name = prefix ^ name,
                               id = id, names = names,
                               termination = Option.map snd (Lib.assoc1 name termination),
                               loop = Option.map snd (Lib.assoc1 name loops)})
            handle Interrupt => raise Interrupt
                 | e => case unsupported_message e of
                          SOME m => Unsupported m
                        | NONE => Failed (General.exnMessage e)
      in
        {name = name, outcome = outcome,
         seconds = Time.toReal (Timer.checkRealTimer timer)}
      end
  in
    map run (call_order ids calls)
  end

end
