(*
 * smt/rewrite_trivial.ml --- Rewrite trivialities.
 *
 * Author: Hern\'an Vanzetto <hernan.vanzetto@inria.fr>
 *
 * Copyright (C) 2011-2020  INRIA and Microsoft Corporation
 *)

open Ext
open Property
open Expr.T
open List

module B = Builtin
module T = Typ_t
module Smt = Smtcommons

(** Given [a] and [b] where [a <= b], it returns [a, a+1, a+2, ..., b] *)
let rec range2set a b =
  if a <= b
    then (Num (string_of_int a,"") %% []) :: range2set (a+1) b
    else []

(** Simplify trivialities, flatten conj/disjunctions *)
let rec rw e =
(* Util.eprintf "rw: %a" (Expr.Fmt.pp_print_expr (Deque.empty, Ctx.dot)) e ; *)
  let mk x = { e with core = x } in
  let build ex = match ex.core with a -> a |> mk in                             (** mantains e's original properties, especially [Boolify.boolify_prop] *)
  let apply op e1 e2 = Apply (Internal op |> mk, [e1 ; e2]) |> mk in
  let tla_true = Internal B.TRUE |> mk in
  let tla_false = Internal B.FALSE |> mk in
  let lAnd es = Smt.flatten_conj (List (And, es) |> mk) in
  let lOr es = Smt.flatten_disj (List (Or, es) |> mk) in
  let apply1 op ex = Apply (Internal op |> mk, [ex]) |> mk in
  let apply2 op e1 e2 = Apply (Internal op |> mk, [e1 ; e2]) |> mk in
  let eq x y = apply2 B.Eq x y in
  let neg x = apply1 B.Neg x in
  let str_is_int x = try int_of_string x = int_of_string x with _ -> false in
  let str_is_nat x = try int_of_string x >= 0 with _ -> false in
  let mk_num n = Num (string_of_int n,"") |> mk in
  let string_of_float' x = Str.replace_first (Str.regexp "^\\(.*\\)\\.$") "\\1" (string_of_float x) in
  let is_string e = match e.core with String _ -> true | _ -> false in
  let sort_string_exp e1 e2 =
    match e1.core, e2.core with
    | String s1, String s2 -> String.compare s1 s2
    | _ -> -1
  in
  match e.core with
  | List (_, [e]) -> rw (build e)
  | List (And, es) -> lAnd (map rw es)
  | List (Or, es) -> lOr (map rw es)
  | Apply ({core = Internal op}, [x ; y]) ->
    let x = rw x in
    let y = rw y in
    begin match op, x.core, y.core with
    | B.Implies, Internal B.FALSE, _ -> tla_true
    | B.Implies, Internal B.TRUE, _ -> build y
    | B.Implies, _, Internal B.TRUE -> tla_true
    | B.Conj, _, _ -> lAnd [x ; y]
    | B.Disj, _, _ -> lOr [x ; y]
    | B.Mem, Internal (B.TRUE | B.FALSE), Internal B.BOOLEAN -> tla_true
    | B.Cup, _, SetEnum [] -> x
    | B.Cup, SetEnum [], _ -> y
    | B.Cup, SetEnum es, SetEnum fs -> SetEnum (Smt.remove_repeated (es @ fs)) |> mk
    | B.Cap, _, SetEnum [] -> y
    | B.Cap, SetEnum [], _ -> x
    | B.Cap, SetEnum es, SetEnum fs ->
      SetEnum (fold_left (fun r e -> if exists (Expr.Eq.expr e) fs then e :: r else r) [] es) |> mk
    | B.Setminus, _, SetEnum [] -> x
    | B.Setminus, SetEnum [], _ -> x
    | B.Mem, Num (m,""), Internal B.Int when str_is_int m -> tla_true
    | B.Mem, Num (m,""), Internal B.Nat when str_is_nat m -> tla_true
    | (B.Eq | B.Equiv), _, _ when Expr.Eq.expr x y -> tla_true
    | B.Neq, _, _ when Expr.Eq.expr x y -> tla_false
    | (B.Eq | B.Equiv), _, Internal B.TRUE  when T.is_hard_bool x -> build x
    | (B.Eq | B.Equiv), Internal B.TRUE, _  when T.is_hard_bool y -> build y
    | (B.Eq | B.Equiv), _, Internal B.FALSE when T.is_hard_bool x -> rw (neg x)
    | (B.Eq | B.Equiv), Internal B.FALSE, _ when T.is_hard_bool y -> rw (neg y)
    | B.Eq, Num (n,""), Num (m,"") -> if n = m then tla_true else tla_false
    | B.Eq, String s1, String s2 -> if s1 = s2 then tla_true else tla_false
    | B.Eq, Tuple t1, Tuple t2 ->
      begin
        try lAnd (map (fun (x,y) -> eq x y) (combine t1 t2))
        with _ -> tla_false
      end

    (** Trivial arithmetic rules, where no context is needed *)
    | B.Gteq, _, _ -> apply B.Lteq y x |> rw
    | B.Gt, _, _ -> apply B.Lt y x |> rw
    | B.Plus,      Num (x,""), Num (y,"") when str_is_int x && str_is_int y -> mk_num ((int_of_string x) + (int_of_string y))
    | B.Minus,     Num (x,""), Num (y,"") when str_is_int x && str_is_int y -> mk_num ((int_of_string x) - (int_of_string y))
    | B.Times,     Num (x,""), Num (y,"") when str_is_int x && str_is_int y -> mk_num ((int_of_string x) * (int_of_string y))
    | B.Quotient,  Num (x,""), Num (y,"") when str_is_int x && str_is_int y && int_of_string y > 0 ->
                                                                               mk_num ((int_of_string x) / (int_of_string y)) (* integer division *)
    | B.Remainder, Num (x,""), Num (y,"") when str_is_int x && str_is_int y && int_of_string y > 0 ->
                                                                               mk_num ((int_of_string x) mod (int_of_string y))
    | B.Ratio,     Num (x,""), Num (y,"") when str_is_int x && str_is_int y && int_of_string y <> 0 ->
                                                                               Num (string_of_float' ((float_of_string x) /. (float_of_string y)),"") |> mk
    | B.Exp,       Num (x,""), Num (y,"") when str_is_int x && str_is_int y -> Num (string_of_float' ((float_of_string x) ** (float_of_string y)),"") |> mk
    | B.Lt,        Num (x,""), Num (y,"") when str_is_int x && str_is_int y -> if (try (int_of_string x) <  (int_of_string y) with _ -> false) then tla_true else tla_false
    | B.Lteq,      Num (x,""), Num (y,"") when str_is_int x && str_is_int y -> if (try (int_of_string x) <= (int_of_string y) with _ -> false) then tla_true else tla_false
    (* | B.Gt,        Num (x,""), Num (y,"") when str_is_int x && str_is_int y -> if (try (int_of_string y) <  (int_of_string x) with _ -> false) then tla_true else tla_false *)
    (* | B.Gteq,      Num (x,""), Num (y,"") when str_is_int x && str_is_int y -> if (try (int_of_string y) <= (int_of_string x) with _ -> false) then tla_true else tla_false *)

    | B.Subseteq, _, _  when Expr.Eq.expr x y -> tla_true
    | B.Range, Num (a,""), Num (b,"") ->
      SetEnum (range2set (int_of_string a) (int_of_string b)) |> mk |> rw
    | B.Range, _, _ when Expr.Eq.expr x y -> SetEnum [x] |> mk
    | B.Cat, _, Tuple [] -> rw x
    | B.Cat, Tuple [], _ -> rw y
    | B.Append, Tuple [], _ -> Tuple [y] |> mk |> rw
    | _ -> apply op x y
    end
  | Apply ({core = Internal op} as o, [ex]) ->
    let ex = rw ex in
    begin match op, ex.core with
    | B.Neg, Internal B.TRUE  -> tla_false
    | B.Neg, Internal B.FALSE -> tla_true
    | B.Neg, Apply ({core = Internal B.Neg}, [x]) when T.is_hard_bool x -> build x
    | B.Uminus, Num (n,"") -> Num ("-"^n,"") @@ ex
    | B.Tail, Tuple [] -> Tuple [] |> mk
    (* | B.SUBSET, SetEnum es -> SetEnum (map (fun xs -> SetEnum xs |> mk) (all_perms es)) |> mk *)
    | _ -> Apply (o, [ex]) |> mk
    end
  | Apply (f, es) ->
    Apply (rw f, map rw es) |> mk
  | Quant (q, bs, ex) ->
    let ex = rw ex in
    begin match q, bs, ex.core with
    | Forall, _,                      Internal B.TRUE  -> tla_true
    | Forall, (_, _, No_domain) :: _, Internal B.FALSE -> tla_false
    | Exists, _,                      Internal B.FALSE -> tla_false
    | Exists, (_, _, No_domain) :: _, Internal B.TRUE  -> tla_true
    | _ -> Quant (q, rw_bs bs, rw ex) |> mk
    end
  | If (c, t, f) ->
    let c = rw c in
    let t = rw t in
    let f = rw f in
    if Expr.Eq.expr t f then build t else
    begin match c.core with
    | Internal B.TRUE -> build t
    | Internal B.FALSE -> build f
    | _ -> If (c,t,f) |> mk
    end
  | SetEnum es when List.for_all is_string es ->
    SetEnum (List.sort ~cmp:sort_string_exp es) @@ e
  | FcnApp (f, es)    -> FcnApp (rw f, map rw es) |> mk
  | Dot (r, h)        -> Dot (rw r, h) |> mk
  | Tuple es          -> Tuple (map rw es) |> mk
  | Record rs         -> Record (map (fun (h,e) -> h, rw e) rs) |> mk
  | SetOf (ex, bs)    -> SetOf (rw ex, rw_bs bs) |> mk
  | SetSt (_, {core = SetEnum []}, _) -> SetEnum [] |> mk
  | SetSt (h, dom, p) -> SetSt (h, rw dom, rw p) |> mk
  | SetEnum es        -> SetEnum (map rw es) |> mk
  | Arrow (x, y)      -> Arrow (rw x, rw y) |> mk
  | Rect es           -> Rect (map (fun (h,e) -> h, rw e) es) |> mk
  | Product es        -> Product (map rw es) |> mk
  | Fcn (bs, ex)      -> Fcn (rw_bs bs, rw ex) |> mk
  | Except (f, exs) ->
    let rw_ex = function Except_apply ea -> Except_apply (rw ea) | Except_dot h -> Except_dot h in
    let exs = map (fun (es,ex) -> map rw_ex es, rw ex) exs in
    Except (rw f, exs) |> mk
  (* | Sequent seq -> rw (Smt.unroll_seq seq) *)
  | Parens (ex,_) -> rw (build ex)
  | Choose (h, Some d, ex) -> Choose (h, Some (rw d), rw ex) |> mk
  | Choose (h, None, ex) -> Choose (h, None, rw ex) |> mk
  | Case (es, o) ->
    let es = map (fun (p,e) -> rw p, rw e) es in
    let o = match o with Some o -> Some (rw o) | None -> None in
    Case (es, o) |> mk
  | Lambda (xs, ex) -> Lambda (xs, rw ex) |> mk
  | _ -> e
and rw_bs bs =
  let faux = function
    | (v, k, Domain d) -> (v, k, Domain (rw d))
    | b -> b
  in map faux bs
;;
