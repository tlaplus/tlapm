(*
 * abstractor.ml --- make an abstract version of an expression
 *
 * Copyright (C) 2010  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev$";;

open Property;;
open Expr.T;;

(* TLAPM expressions and DeBruijn indices

Indices start at 1: the innermost quantifier is represented by 1.

Binders are:
Lambda -- (l, body) : binds [List.length l] variables in body
Sequent -- {ctx, act} : binds [Deque.length ctx] variables in body
           ** each variable is bound in the rest of the context
Let -- (l, body) : binds [List.length l] variables in body
           ** each variable is bound in the rest of the list
Quant -- (q, l, body) : binds [List.length l] variables in body (not in l)
Tquant -- (q, l, body) : binds [List.length l] variables in body
Choose -- (h, o, body) : binds 1 variable in body (not in o)
SetSt -- (h, e1, e2) : binds 1 variable in e2 (not in e1)
SetOf -- (body, l) : binds (List.length l) variables in body (not in l)
Fcn -- (l, body) : binds (List.length l) variables in body (not in l)

*)


let list f l env =
  List.fold_left (fun lv x -> min lv (f x env)) max_int l
;;

(* [get_level e 0] returns the minimum index of all free
   variables in [e], or [max_int] if [e] is closed.
*)

let rec get_level e env =
  match e.core with
  | Ix i -> if i > env then i - env else max_int
  | Opaque _ -> max_int
  | Internal _ -> max_int
  | Lambda (l, e1) -> get_level e1 (env + List.length l)
  | Sequent {context=c; active=a} -> get_level_sequent c a env
  | Bang (e, l) -> min (get_level e env) (list get_level_selector l env)
  | Apply (f, args) -> list get_level (f :: args) env
  | With (e1, _) -> get_level e1 env
  | If (e1, e2, e3) -> list get_level [e1; e2; e3] env
  | List (_, l) -> list get_level l env
  | Let (d, e1) ->
     let f (res, env) e = (min res (get_level_def e env), env + 1) in
     let (ldefs, env1) = List.fold_left f (max_int, env) d in
     min ldefs (get_level e1 env1)
  | Quant (_, l, e1) -> get_level_quant l e1 env
  | Tquant (_, l, e1) -> get_level e1 (env + List.length l)
  | Choose (_, Some b, e1) ->
     min (get_level b env) (get_level e1 (env + 1))
  | Choose (_, None, e1) -> get_level e1 (env + 1)
  | SetSt (_, b, e1) ->
     min (get_level b env) (get_level e1 (env + 1))
  | SetOf (e1, bs) | Fcn (bs, e1) ->
     let l1 = get_level e1 (env + List.length bs) in
     min l1 (list get_level_bound_domain bs env)
  | SetEnum (l) | Product (l) | Tuple (l) -> list get_level l env
  | FcnApp (e1, l) -> list get_level (e1 :: l) env
  | Arrow (e1, e2) -> min (get_level e1 env) (get_level e2 env)
  | Rect (l) | Record (l) -> list get_level (List.map snd l) env
  | Except (e1, l) -> min (get_level e1 env) (list get_level_exspec l env)
  | Dot (e1, _) -> get_level e1 env
  | Sub (_, e1, e2) | Tsub (_, e1, e2) | Fair (_, e1, e2) ->
     min (get_level e1 env) (get_level e2 env)
  | Case (l, None) -> list get_level_case l env
  | Case (l, Some e1) -> min (list get_level_case l env) (get_level e1 env)
  | String _ -> max_int
  | Num _ -> max_int
  | At _ -> max_int
  | Parens (e1, _) -> get_level e1 env

and get_level_quant l e env =
  let f m b = min m (get_level_bound_domain b env) in
  min (List.fold_left f max_int l) (get_level e (env + List.length l))

and get_level_sequent c a env =
  match Deque.front c with
  | None -> get_level a env
  | Some ({core = Fact (f, _)}, c1) ->
     min (get_level f env) (get_level_sequent c1 a (env + 1))
  | Some ({core = Defn (d, _, _, _)}, c1) ->
     min (get_level_def d env) (get_level_sequent c1 a (env + 1))
  | Some ({core = (Fresh _ | Flex _)}, c1) -> get_level_sequent c1 a (env + 1)

and get_level_selector s env =
  match s with
  | Sel_inst el | Sel_lab (_, el) -> list get_level el env
  | _ -> max_int

and get_level_exspec (l, e) env =
  min (get_level e env) (list get_level_expoint l env)

and get_level_expoint p env =
  match p with
  | Except_dot _ -> max_int
  | Except_apply e -> get_level e env

and get_level_bound_domain b env =
  match b with
  | (_, _, (No_domain | Ditto)) -> max_int
  | (_, _, Domain e) -> get_level e env

and get_level_def x env =
  match x.core with
  | Recursive (_, _) -> max_int
  | Operator (_, e) -> (get_level e env)
  | Bpragma (_,e,_) ->  (get_level e env)
  | Instance _ -> assert false

and get_level_case (e1, e2) env = min (get_level e1 env) (get_level e2 env)
;;


let shift d env i =
  if i > env then (assert (i - d > env); i - d) else i
;;

(* [equal d1 d2 0 e1 e2] returns [true] iff [e1] shifted by [d1]
   and [e2] shifted by [d2] are equal modulo alpha-conversion
   and ignoring properties and proof methods.
   Shifting by d means decrementing all free variables by d.
*)

let rec equal_list f l1 l2 =
  match l1, l2 with
  | [], [] -> true
  | (h1 :: t1), (h2 :: t2) -> equal_list f t1 t2 && f h1 h2
  | _, _ -> false
;;

let equal_option f o1 o2 =
  match o1, o2 with
  | None, None -> true
  | Some x1, Some x2 -> f x1 x2
  | _, _ -> false
;;

let rec equal d1 d2 env e1 e2 =
  let c1 = e1.core in
  let c2 = e2.core in
  match c1, c2 with
  | Ix i1, Ix i2 -> shift d1 env i1 = shift d2 env i2
  | Opaque _, Opaque _ -> c1 = c2
  | Internal _, Internal _ -> c1 = c2
  | Lambda (l1, e1), Lambda (l2, e2) ->
     equal_list (fun x1 x2 -> snd x1 = snd x2) l1 l2
     && equal d1 d2 (env + List.length l1) e1 e2
  | Sequent s1, Sequent s2 -> equal_sequent d1 d2 env s1 s2
  | Bang (e1, l1), Bang (e2, l2) ->
     equal d1 d2 env e1 e2 && equal_list (equal_sel d1 d2 env) l1 l2
  | Apply (e1, l1), Apply (e2, l2) ->
     equal d1 d2 env e1 e2 && equal_list (equal d1 d2 env) l1 l2
  | With (e1, m1), With (e2, m2) -> equal d1 d2 env e1 e2
  | If (a1, b1, c1), If (a2, b2, c2) ->
     equal d1 d2 env a1 a2 && equal d1 d2 env b1 b2 && equal d1 d2 env c1 c2
  | List (b1, l1), List (b2, l2) -> b1 = b2 && equal_list (equal d1 d2 env) l1 l2
  | Let (df1, e1), Let (df2, e2) ->
     equal_list (equal_defn d1 d2 env) df1 df2 && equal d1 d2 env e1 e2
  | Quant (q1, b1, e1), Quant (q2, b2, e2) ->
     q1 = q2
     && equal_list (equal_bound d1 d2 env) b1 b2
     && equal d1 d2 (env + List.length b1) e1 e2
  | Tquant (q1, h1, e1), Tquant (q2, h2, e2) ->
     q1 = q2
     && List.length h1 = List.length h2
     && equal d1 d2 (List.length h1) e1 e2
  | Choose (h1, o1, e1), Choose (h2, o2, e2) ->
     equal_option (equal d1 d2 env) o1 o2 && equal d1 d2 (env + 1) e1 e2
  | SetSt (h1, a1, b1), SetSt (h2, a2, b2) ->
     equal d1 d2 env a1 a2 && equal d1 d2 (env + 1) b1 b2
  | SetOf (e1, b1), SetOf (e2, b2) ->
     equal d1 d2 (env + List.length b1) e1 e2
     && equal_list (equal_bound d1 d2 env) b1 b2
  | SetEnum (l1), SetEnum (l2) -> equal_list (equal d1 d2 env) l1 l2
  | Product (l1), Product (l2) -> equal_list (equal d1 d2 env) l1 l2
  | Tuple (l1), Tuple (l2) -> equal_list (equal d1 d2 env) l1 l2
  | Fcn (b1, e1), Fcn (b2, e2) ->
     equal_list (equal_bound d1 d2 env) b1 b2
     && equal d1 d2 (env + List.length b1) e1 e2
  | FcnApp (e1, l1), FcnApp (e2, l2) ->
     equal d1 d2 env e1 e2 && equal_list (equal d1 d2 env) l1 l2
  | Arrow (a1, b1), Arrow (a2, b2) ->
     equal d1 d2 env a1 a2 && equal d1 d2 env b1 b2
  | Rect (l1), Rect (l2) ->
     equal_list (fun (s1, e1) (s2, e2) -> s1 = s2 && equal d1 d2 env e1 e2) l1 l2
  | Record (l1), Record (l2) ->
     equal_list (fun (s1, e1) (s2, e2) -> s1 = s2 && equal d1 d2 env e1 e2) l1 l2
  | Except (e1, l1), Except (e2, l2) ->
     equal d1 d2 env e1 e2 && equal_list (equal_exspec d1 d2 env) l1 l2
  | Dot (e1, s1), Dot (e2, s2) -> equal d1 d2 env e1 e2 && s1 = s2
  | Sub (o1, a1, b1), Sub (o2, a2, b2) ->
     o1 = o2 && equal d1 d2 env a1 a2 && equal d1 d2 env b1 b2
  | Tsub (o1, a1, b1), Tsub (o2, a2, b2) ->
     o1 = o2 && equal d1 d2 env a1 a2 && equal d1 d2 env b1 b2
  | Fair (o1, a1, b1), Fair (o2, a2, b2) ->
     o1 = o2 && equal d1 d2 env a1 a2 && equal d1 d2 env b1 b2
  | Case (l1, o1), Case (l2, o2) ->
     let eq_case (a1, b1) (a2, b2) =
       equal d1 d2 env a1 a2 && equal d1 d2 env b1 b2
     in
     equal_list eq_case l1 l2 && equal_option (equal d1 d2 env) o1 o2
  | Parens (e1, _), Parens (e2, _) -> equal d1 d2 env e1 e2
  | _, _ -> false

and equal_sequent d1 d2 env s1 s2 =
  let c1 = Deque.to_list s1.context in
  let c2 = Deque.to_list s2.context in
  let cmp env h1 h2 =
    match h1.core, h2.core with
    | Fresh (_, sh1, k1, dom1), Fresh (_, sh2, k2, dom2) ->
       (sh1 = sh2 && k1 = k2 && equal_hdom d1 d2 env dom1 dom2, env + 1)
    | Flex _, Flex _ -> (true, env + 1)
    | Defn (df1, _, _, _), Defn (df2, _, _, _) ->
       (equal_defn d1 d2 env df1 df2, env + 1)
    | Fact (e1, _), Fact (e2, _) -> (equal d1 d2 env e1 e2, env)
    | _, _ -> (false, env)
  in
  let f (acc, env) h1 h2 = if acc then cmp env h1 h2 else (false, env) in
  let (same_ctx, env2) = List.fold_left2 f (true, env) c1 c2 in
  same_ctx && equal d1 d2 env2 s1.active s2.active

and equal_hdom d1 d2 env dom1 dom2 =
  match dom1, dom2 with
  | Unbounded, Unbounded -> true
  | Bounded (e1, _), Bounded (e2, _) -> equal d1 d2 env e1 e2
  | _, _ -> false

and equal_sel d1 d2 env s1 s2 =
  match s1, s2 with
  | Sel_down, Sel_down -> true
  | Sel_num i1, Sel_num i2 -> i1 = i2
  | Sel_left, Sel_left -> true
  | Sel_right, Sel_right -> true
  | Sel_at, Sel_at -> true
  | Sel_inst l1, Sel_inst l2 -> equal_list (equal d1 d2 env) l1 l2
  | Sel_lab (st1, l1), Sel_lab (st2, l2) ->
     st1 = st2 && equal_list (equal d1 d2 env) l1 l2
  | _, _ -> false

and equal_defn d1 d2 env df1 df2 =
  match df1.core, df2.core with
  | Operator (_, e1), Operator (_, e2) -> equal d1 d2 env e1 e2
  | Instance (_, i1), Instance (_, i2) -> equal_instance d1 d2 env i1 i2
  | _, _ -> false

and equal_instance d1 d2 env i1 i2 =
  let cmp (_, e1) (_, e2) = equal d1 d2 env e1 e2 in
  i1.inst_mod = i2.inst_mod
  && List.length i1.inst_args = List.length i2.inst_args
  && equal_list cmp i1.inst_sub i2.inst_sub

and equal_bound d1 d2 env (_, k1, dom1) (_, k2, dom2) =
  match dom1, dom2 with
  | No_domain, No_domain -> k1 = k2
  | Domain (e1), Domain (e2) -> k1 = k2 && equal d1 d2 env e1 e2
  | Ditto, Ditto -> k1 = k2
  | _, _ -> false

and equal_exspec d1 d2 env (l1, e1) (l2, e2) =
  equal_list (equal_expoint d1 d2 env) l1 l2 && equal d1 d2 env e1 e2

and equal_expoint d1 d2 env p1 p2 =
  match p1, p2 with
  | Except_dot (s1), Except_dot (s2) -> s1 = s2
  | Except_apply (e1), Except_apply (e2) -> equal d1 d2 env e1 e2
  | _, _ -> false
;;

let option_map f o =
  match o with
  | Some x -> Some (f x)
  | None -> None
;;

module BI = Builtin;;

let cur = ref 0;;
let gensym () = incr cur; !cur;;

(* spine = still in the spine ?
   env = local environment (i.e. number of binders between the spine and here)
   stk = stack of references to (expr * hint) list for the spine

TO DO: generaliser la spine aux \E sous negations / a gauche des =>

f returns true if the expression is handled by the back-end,
false if it must be abstracted away

*)

let push (len, bot, list) = (len + 1, bot, ref [] :: list);;
let length (len, _, _) = len;;
let get (_, bot, list) n =
  let rec spin list n =
    match list with
    | [] -> bot
    | h :: _ when n = 1 -> h
    | _ :: t -> spin t (n-1)
  in
  spin list n
;;

let rec abst f spine stk env e =
  if f e then begin
    let abs e = abst f false stk env e in
    let newcore =
      match e.core with
      | Apply ({core = Internal (BI.Conj | BI.Disj)} as conn, [e1; e2]) ->
         Apply (conn, [abst f spine stk env e1; abst f spine stk env e2])
      | Apply ({core = Internal BI.Implies} as conn, [e1; e2]) ->
         Apply (conn, [abs e1; abst f spine stk env e2])

      | Ix _ | Opaque _ | Internal _ -> e.core
      | Lambda (l, e1) ->
         Lambda (l, abst f false stk (env + List.length l) e1)
      | Sequent {context = c; active = a} -> abst_sequent f spine stk env c a
      | Bang (e1, l) -> Bang (abs e1, List.map (abst_sel f stk env) l)
      | Apply (e1, l) -> Apply (abs e1, List.map abs l)
      | With (e1, m) -> With (abst f spine stk env e1, m)
      | If (e1, e2, e3) -> If (abs e1, abs e2, abs e3)
      | List (b, l) -> List (b, List.map (abst f spine stk env) l)
      | Let (l, e) -> abst_let f stk env l e
      | Quant (Forall, l, e1) ->
         assert (env = 0);
         Quant (Forall, List.map (abst_bound f stk env) l,
                abst f spine (push stk) env e1)
      | Quant (Exists, l, e1) ->
         Quant (Exists, List.map (abst_bound f stk env) l,
                abst f false stk (env + List.length l) e1)
      | Tquant (q, l, e1) ->
         Tquant (q, l, abst f false stk (env + List.length l) e1)
      | Choose (h, o, e1) ->
         Choose (h, option_map abs o, abst f false stk (env + 1) e1)
      | SetSt (h, e1, e2) ->
         SetSt (h, abs e1, abst f false stk (env + 1) e2)
      | SetOf (e1, l) ->
         SetOf (abst f false stk (env + List.length l) e1,
                List.map (abst_bound f stk env) l)
      | SetEnum (l) -> SetEnum (List.map abs l)
      | Product (l) -> Product (List.map abs l)
      | Tuple (l) -> Tuple (List.map abs l)
      | Fcn (l, e1) -> Fcn (List.map (abst_bound f stk env) l,
                            abst f false stk (env + List.length l) e1)
      | FcnApp (e1, l) -> FcnApp (abs e1, List.map abs l)
      | Arrow (e1, e2) -> Arrow (abs e1, abs e2)
      | Rect (l) -> Rect (List.map (fun (s, e1) -> (s, abs e1)) l)
      | Record (l) -> Record (List.map (fun (s, e1) -> (s, abs e1)) l)
      | Except (e1, l) -> Except (abs e1, List.map (abst_exspec f stk env) l)
      | Dot (e1, s) -> Dot (abs e1, s)
      | Sub (op, e1, e2) -> Sub (op, abs e1, abs e2)
      | Tsub (op, e1, e2) -> Tsub (op, abs e1, abs e2)
      | Fair (op, e1, e2) -> Fair (op, abs e1, abs e2)
      | Case (l, o) ->
         Case (List.map (fun (x, y) -> (abs x, abs y)) l, option_map abs o)
      | String _ -> e.core
      | Num _ -> e.core
      | At _ -> e.core
      | Parens (e1, p) -> Parens (abst f spine stk env e1, p)
    in newcore @@ e
  end else begin
    let delta = get_level e 0 in
    if delta > env then begin
      let r = get stk (delta - env) in
      let rec spin l =
        match l with
        | [] ->
            let v = Ix (gensym () + env + length stk) in
            r := (e, delta, v) :: !r;
            v @@ nowhere
        | (e2, d2, v) :: _ when equal delta d2 0 e e2 -> v @@ nowhere
        | _ :: t -> spin t
      in
      spin !r
    end else begin
      (* We cannot abstract this expression because it uses a non-spine
         variable.  Intead of raising an exception, we leave the expression
         untouched, so that the back-end can choose to ignore it.  For
         example, Cooper does it for the antecedents of implications. *)
      e
    end
  end

(* In a sequent, each binding is in the scope of the previous ones *)
and abst_sequent f spine stk env c a =
  let g (stk, env, q) hyp =
    let (stk1, env1) = if spine then (push stk, env) else (stk, env + 1)
    in
    let h1 = match hyp.core with
      | Fresh (h, s, k, d) -> Fresh (h, s, k, abst_hdom f stk env d)
      | Flex _ -> hyp.core
      | Defn (d, w, v, x) -> Defn (abst_defn f stk env d, w, v, x)
      | Fact (e1, v) -> Fact (abst f false stk env e1, v)
    in
    (stk1, env1, Deque.snoc q (h1 @@ hyp))
  in
  let (stk1, env1, q1) = Deque.fold_left g (stk, env, Deque.empty) c in
  Sequent { context = q1; active = abst f spine stk1 env1 a }

and abst_sel f stk env s =
  match s with
  | Sel_down | Sel_num _ | Sel_left | Sel_right | Sel_at -> s
  | Sel_inst (l) -> Sel_inst (List.map (abst f false stk env) l)
  | Sel_lab (st, l) -> Sel_lab (st, List.map (abst f false stk env) l)

and abst_bound f stk env b =
  match b with
  | (_, _, (No_domain | Ditto)) -> b
  | (h, k, Domain e1) -> (h, k, Domain (abst f false stk env e1))

(* In a let, each binding is in the scope of the previous ones *)
and abst_let f stk env l e =
  let g (env, q) def = (env+1, abst_defn f stk env def :: q) in
  let (env1, q1) = List.fold_left g (env, []) l in
  Let (List.rev q1, abst f false stk env1 e)

and abst_exspec f stk env (l, e) =
  (List.map (abst_expoint f stk env) l, abst f false stk env e)

and abst_expoint f stk env p =
  match p with
  | Except_dot _ -> p
  | Except_apply e1 -> Except_apply (abst f false stk env e1)

and abst_hdom f stk env d =
  match d with
  | Unbounded -> Unbounded
  | Bounded (e1, v) -> Bounded (abst f false stk env e1, v)

and abst_defn f stk env d =
  let d1 =
    match d.core with
    | Recursive (nm, shp) -> Recursive (nm, shp)
    | Operator (h, e1) -> Operator (h, abst f false stk env e1)
    | Bpragma (h, e1, l) -> Bpragma (h, abst f false stk env e1, l)
    | Instance (h, i) -> assert false
  in d1 @@ d
;;

let abstract f e =
  cur := 0;
(*  if Params.debugging "abs" then
    Util.eprintf "Before abstraction first pass:@\n  @[<b0>%a@]@."
      (Expr.Fmt.pp_print_expr (Deque.empty, Ctx.dot)) e;
  let e = first_pass e in
    if Params.debugging "abs" then
      Util.eprintf "After abstraction first pass:@\n  @[<b0>%a@]@."
                   (Expr.Fmt.pp_print_expr (Deque.empty, Ctx.dot)) e;*)
  let e1 = abst f true (0, ref [], []) 0 e in
  let rec spin ee n =
    if n = 0 then ee else begin
      let hint = Printf.sprintf "__abs_%d" n @@ nowhere in
      spin (Quant (Forall, [(hint, Constant, No_domain)], ee) @@ nowhere) (n-1)
    end
  in
  spin e1 !cur
;;
