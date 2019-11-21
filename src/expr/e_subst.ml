(*
 * expr/subst.ml --- expressions (substitution)
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev$";;

open Ext
open Property
open E_t

module Fmt = E_fmt;;

type sub =
  | Shift of int
  | Cons of expr * sub
  | Compose of sub * sub
  | Bump of int * sub

let shift n = Shift n
let scons e s = Cons (e, s)
let ssnoc s e = Cons (e, s)
let compose s t = Compose (s, t)

let bumpn n = function
  | Bump (k, s) -> Bump (k + n, s)
  | s -> Bump (n, s)

let bump s = bumpn 1 s

let rec app_expr s oe = match oe.core with
  | ( Internal _ | Opaque _ | String _ | Num _ | At _ ) ->
      oe
  | Ix n ->
      app_ix s (n @@ oe)
  | Apply (op, fs) ->
      normalize (app_expr s op) (app_exprs s fs) @@ oe
  | Bang (e, sels) ->
      Bang (app_expr s e, List.map (app_sel s) sels) @@ oe
  | Lambda (vs, e) ->
      Lambda (vs, app_expr (bumpn (List.length vs) s) e) @@ oe
  | Let (ds, e) ->
      let (s, ds) = app_defns s ds in
      Let (ds, app_expr s e) @@ oe
  | Sequent sq ->
      Sequent (app_sequent s sq) @@ oe
  | With (e, meth) ->
      With (app_expr s e, meth) @@ oe
  | If (e, f, g) ->
      If (app_expr s e, app_expr s f, app_expr s g) @@ oe
  | List (q, es) ->
      List (q, List.map (app_expr s) es) @@ oe
  | Quant (q, bs, e) ->
      let (s, bs) = app_bounds s bs in
      Quant (q, bs, app_expr s e) @@ oe
  | Tquant (q, vs, e) ->
      Tquant (q, vs, app_expr (bumpn (List.length vs) s) e) @@ oe
  | Choose (v, optdom, e) ->
      let optdom = Option.map (app_expr s) optdom in
      Choose (v, optdom, app_expr (bump s) e) @@ oe
  | SetSt (v, dom, e) ->
      SetSt (v, app_expr s dom, app_expr (bump s) e) @@ oe
  | SetOf (e, bs) ->
      let (s, bs) = app_bounds s bs in
      SetOf (app_expr s e, bs) @@ oe
  | SetEnum es ->
      SetEnum (List.map (app_expr s) es) @@ oe
  | Arrow (a, b) ->
      Arrow (app_expr s a, app_expr s b) @@ oe
  | Fcn (bs, e) ->
      let (s, bs) = app_bounds s bs in
      Fcn (bs, app_expr s e) @@ oe
  | FcnApp (f, es) ->
      FcnApp (app_expr s f, List.map (app_expr s) es) @@ oe
  | Product es ->
      Product (List.map (app_expr s) es) @@ oe
  | Tuple es ->
      Tuple (List.map (app_expr s) es) @@ oe
  | Rect fs ->
      Rect (List.map (fun (v, e) -> (v, app_expr s e)) fs) @@ oe
  | Record fs ->
      Record (List.map (fun (v, e) -> (v, app_expr s e)) fs) @@ oe
  | Except (e, xs) ->
      Except (app_expr s e, app_xs s xs) @@ oe
  | Dot (e, f) ->
      Dot (app_expr s e, f) @@ oe
  | Sub (m, e, f) ->
      Sub (m, app_expr s e, app_expr s f) @@ oe
  | Tsub (m, e, f) ->
      Tsub (m, app_expr s e, app_expr s f) @@ oe
  | Fair (m, e, f) ->
      Fair (m, app_expr s e, app_expr s f) @@ oe
  | Case (arms, oth) ->
      Case (List.map (fun (e, f) -> (app_expr s e, app_expr s f)) arms,
            Option.map (app_expr s) oth) @@ oe
  | Parens (e, rig) -> Parens (app_expr s e, rig) @@ oe

and app_exprs s es =
  List.map (fun e -> app_expr s e) es

and normalize ?(cx = Deque.empty) op args = match op.core with
  | Lambda (vs, e) ->
      if List.length vs <> List.length args then begin
        Util.eprintf ~at:op
          "@[<v0>Arity mismatch:@,op =@,  %a@,args =@,  @[<v0>%a@]@]@."
          (Fmt.pp_print_expr (cx, Ctx.dot)) op
          (Fmtutil.pp_print_delimited
             (Fmt.pp_print_expr (cx, Ctx.dot))) args ;
        failwith "Expr.Subst.normalize"
      end else begin
        let sub = List.fold_left ssnoc (shift 0) args in
        (app_expr sub e).core
      end
  | Apply (op, oargs) ->
      Apply (op, oargs @ args)
  | _ -> begin
      match args with
        | [] -> op.core
        | _ -> Apply (op, args)
    end

and app_sel s = function
  | Sel_inst args ->
      Sel_inst (app_exprs s args)
  | Sel_lab (l, args) ->
      Sel_lab (l, app_exprs s args)
  | sel -> sel

and app_bdom s = function
  | Domain d -> Domain (app_expr s d)
  | d -> d

and app_bounds s bs =
  let bs = List.map begin
    fun (v, k, dom) -> match dom with
      | Domain d -> (v, k, Domain (app_expr s d))
      | _ -> (v, k, dom)
  end bs in
  let s = bumpn (List.length bs) s in
  (s, bs)

and app_bound s b = match app_bounds s [b] with
  | (s, [b]) -> (s, b)
  | _ -> assert false

and app_xs s xs =
  List.map (fun x -> app_x s x) xs

and app_x s (trail, res) =
  (List.map (function
               | Except_dot s -> Except_dot s
               | Except_apply e -> Except_apply (app_expr s e)) trail,
   app_expr s res)

(* [PERF] this is the hottest function in the PM (ignoring GC) *)
and app_ix s n = match s with
  | Shift m -> Ix (m + n.core) @@ n
  | Cons (op, _) when n.core = 1 -> op.core @@ n
  | Cons (_, s) -> app_ix s (n.core - 1 @@ n)
  | Compose (ss, tt) -> app_expr ss (app_ix tt n)
  | Bump (k, ss) when n.core <= k -> Ix n.core @@ n
  | Bump (k, ss) -> app_expr (Shift k) (app_ix ss (n.core - k @@ n))

and app_defn s d =
  { d with core = app_defn_ s d.core }

and app_defn_ s = function
  | Recursive (nm, shp) -> Recursive (nm, shp)
  | Operator (nm, e) -> Operator (nm, app_expr s e)
  | Instance (nm, inst) -> Instance (nm, app_instance s inst)
  | Bpragma (nm, e, l) -> Bpragma (nm, app_expr s e, l)

and app_defns s = function
  | [] -> (s, [])
  | d :: ds ->
      let d = app_defn s d in
      let (s, ds) = app_defns (bump s) ds in
      (s, d :: ds)

and app_instance s i =
  let s = bumpn (List.length i.inst_args) s in
  { i with inst_sub = List.map (fun (v, e) -> (v, app_expr s e)) i.inst_sub }

and app_sequent s sq =
  let (s, cx) = app_hyps s sq.context in
  { context = cx ; active = app_expr s sq.active }

and app_hyps s cs = match Deque.front cs with
  | None -> (s, Deque.empty)
  | Some (c, cs) ->
      let c = app_hyp s c in
      let (s, cs) = app_hyps (bump s) cs in
      (s, Deque.cons c cs)

and app_hyp s h = match h.core with
  | Fresh (x, shp, lv, b) -> Fresh (x, shp, lv, app_dom s b) @@ h
  | Flex v -> Flex v @@ h
  | Defn (d, wd, us, ex) -> Defn (app_defn s d, wd, us, ex) @@ h
  | Fact (e, us,tm) -> Fact (app_expr s e, us,tm) @@ h

and app_dom s = function
  | Unbounded -> Unbounded
  | Bounded (dom, vis) -> Bounded (app_expr s dom, vis)

let rec app_spine s = function
  | [] -> []
  | e :: es ->
      app_expr s e :: app_spine (bump s) es

open Format
open E_fmt

let pp_print_sub cx ff =
  let rec handle ff s = match s with
    | Shift n ->
        fprintf ff "^%d" n
    | Cons (op, s) ->
        pp_print_expr cx ff op ;
        pp_print_string ff " ." ;
        pp_print_space ff () ;
        handle ff s
    | Compose (s, t) ->
        fprintf ff "(%a) o (%a)" handle s handle t
    | Bump (n, s) ->
        fprintf ff "%d(%a)" n handle s
  in
  fprintf ff "@[<b1>[%a]@]" handle


let extract sq k =
  let prefix : hyp Deque.dq ref = ref Deque.empty in
  let rec scan n hs = match Deque.front hs with
    | None -> failwith "scan"
    | Some (h, hs) ->
        if n = k then (h, hs) else
          begin
            prefix := Deque.snoc !prefix h ;
            scan (n + 1) hs
          end
  in try begin
    let (h, hs) = scan 0 sq.context in
    let e = match h.core with
      | Fact (e, _, _) -> app_expr (shift (Deque.size hs)) e
      | _ -> failwith "exprtract" in
    let (s, hs) = app_hyps (shift (-1)) hs in
    let sq = {
      context = Deque.append !prefix hs ;
      active = app_expr s sq.active ;
    } in
    Some (sq, e)
  end with _ -> None
