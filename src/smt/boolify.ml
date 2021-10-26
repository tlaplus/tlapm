(************************************************************************
*
*  boolify.ml
*
*
*  Created by Hernán Vanzetto on 23 Oct 2013.
*  Copyright (C) 2013-2014  INRIA and Microsoft Corporation
*
************************************************************************)

open Ext
open Property

open Expr.T
open Expr.Subst
open Expr.Visit

open Printf
open List

module B = Builtin
module SMap = Map.Make (String)
module Smt = Smtcommons

(****************************************************************************)

(** Boolify an expression [e]. It wraps [e] with the [boolify] operator. *)
let mk_bool e = Apply (Opaque "boolify" |> noprops, [e]) @@ e
let mk_bool2u e = Apply (Opaque "bool2u" |> noprops, [e]) @@ e

(** [eboo e] = expected Boolean
    [nboo e] = not expected Boolean *)
let rec eboo e =
(* Util.eprintf "## eboo: %a" (Typ_e.pp_print_expr (Deque.empty, Ctx.dot)) e ; *)
  let mk x = { e with core = x } in
  (* let mk_bool x =
(* Util.eprintf "## eboo: %a" (print_prop ()) e ; *)
  (* Printf.eprintf "-- boolified!\n"; *)
    Property.assign { e with core = x } boolify_prop ()
  in *)
  begin match e.core with
  | Apply ({core = Opaque "boolify"}, _) ->                                   (** Do not boolify an already boolified expression. *)
      Property.remove e Smt.boolify_prop
  | Apply ({core = Opaque "tla__isAFcn"} as o, [ex]) ->
      Apply (o, [nboo ex]) @@ e
  | Ix n ->
      e |> mk_bool
  | Opaque s ->
      e |> mk_bool
  | Apply ({core = Ix _ | Opaque _} as f, es) ->
      Apply (nboo f, map nboo es) |> mk |> mk_bool
  | FcnApp (f,es) ->
      FcnApp (nboo f, map nboo es) |> mk |> mk_bool
  | Dot (r, h) ->
      Dot (nboo r, h) |> mk |> mk_bool
  | Choose (h, d, ex) ->
      Choose (h, Option.map nboo d, eboo ex) |> mk |> mk_bool
  | Except (f, exs) ->
      let boo_ex = function Except_apply ea -> Except_apply (nboo ea) | Except_dot h -> Except_dot h in
      let exs = List.map (fun (es,ex) -> List.map boo_ex es, nboo ex) exs in
      Except (nboo f, exs) |> mk
  | Apply ({core = Internal o} as op, es) ->
      begin match o with
      | B.Conj | B.Disj | B.Implies | B.Equiv | B.Neg ->
          Apply (op, map eboo es) |> mk
      | B.Mem | B.Notmem | B.Subseteq | B.Lteq | B.Lt | B.Gteq | B.Gt ->
          Apply (op, map nboo es) |> mk
      | B.Eq | B.Neq ->
          Apply (op, map nboo es) |> mk
      | _ ->
          failwith "Trying to Boolify a non Boolean operator."
      end
  | List (q, es) ->
      List (q, map eboo es) |> mk
  | Quant (q, bs, ex) ->
      Quant (q, nboobs bs, eboo ex) |> mk
  | Internal B.TRUE | Internal B.FALSE ->
      e
  | If (c, t, f) ->
      If (eboo c, eboo t, eboo f) |> mk
  | Case (es, o) ->
      let es = List.map (fun (p,e) -> eboo p, eboo e) es in
      Case (es, Option.map eboo o) |> mk
  | Lambda (xs,ex) -> Lambda (xs, eboo ex) |> mk
  (* | Sequent sq ->
      eboo (Smt.unroll_seq seq) *)
  | Parens (ex,_) -> eboo ex
  (* | Apply (op, es) -> Apply (nboo op, map nboo es) |> mk *)
  | _ ->
     failwith "Trying to Boolify a non Boolean operator."
  end
and nboo e =
(* Util.eprintf "## not-a-boolean: %a" (print_prop ()) e ; *)
  let mk x = { e with core = x } in
  begin match e.core with
  | Apply ({core = Opaque "boolify"}, _) ->
      e |> mk_bool2u
  | Ix _ | Opaque _ -> e
  | FcnApp (f, es) -> FcnApp (nboo f, map nboo es) |> mk
  | Dot (r, h) -> Dot (nboo r, h) |> mk
  | Apply ({core = Internal o} as op, es) ->
      begin match o with
      | B.Conj | B.Disj | B.Implies | B.Equiv | B.Neg ->
          Apply (op, map eboo es) |> mk |> mk_bool2u
      | B.Mem | B.Notmem | B.Subseteq | B.Lteq | B.Lt | B.Gteq | B.Gt ->
          (* failwith "not expected Boolean" *)
          Apply (op, map nboo es) |> mk |> mk_bool2u
      | B.Eq | B.Neq ->
          Apply (op, map nboo es) |> mk |> mk_bool2u
      | B.Range ->
          Apply (op, map nboo es) |> mk
      | _ ->
          Apply (nboo op, map nboo es) |> mk
      end
  | Apply (op, es) -> Apply (nboo op, map nboo es) |> mk
  | Choose (h, d, ex) -> Choose (h, Option.map nboo d, eboo ex) |> mk
  | Tuple es -> Tuple (map nboo es) |> mk
  | Record rs -> Record (List.map (fun (h,e) -> h, nboo e) rs) |> mk
  | SetOf (ex, bs) -> SetOf (nboo ex, nboobs bs) |> mk
  | SetSt (h, dom, ex) -> SetSt (h, nboo dom, eboo ex) |> mk
  | SetEnum es -> SetEnum (map nboo es) |> mk
  | Arrow (e1,e2) -> Arrow (nboo e1, nboo e2) |> mk
  | Expr.T.Fcn (bs, ex) -> Expr.T.Fcn (nboobs bs, nboo ex) |> mk
  | Except (f, exs) ->
      let boo_ex = function Except_apply ea -> Except_apply (nboo ea) | Except_dot h -> Except_dot h in
      let exs = List.map (fun (es,ex) -> List.map boo_ex es, nboo ex) exs in
      Except (nboo f, exs) |> mk
  | Rect rs -> Rect (List.map (fun (h,e) -> h, nboo e) rs) |> mk
  | Product es -> Product (map nboo es) |> mk
  | If (c, t, f) -> If (eboo c, nboo t, nboo f) |> mk
  | Case (es, o) ->
      let es = List.map (fun (p,e) -> eboo p, nboo e) es in
      Case (es, Option.map nboo o) |> mk
  | Lambda (xs,ex) -> Lambda (xs, eboo ex) |> mk
  | Parens (ex,_) -> nboo ex
  | Internal B.TRUE | Internal B.FALSE -> e
  | Internal B.Int | Internal B.Nat | Internal B.Real -> e
  | Internal B.Len | Internal B.Seq | Internal B.Append | Internal B.Tail | Internal B.Cat -> e

  | List (q, es) ->
      List (q, map eboo es) |> mk
  | Quant (q, bs, ex) ->
      Quant (q, nboobs bs, eboo ex) |> mk
  | _ ->
     (* failwith "not expected Boolean" *)
     e
  end
and nboobs bs =
  List.map
    begin function
    | (v, k, Domain d) -> (v, k, Domain (nboo d))
    | b -> b
    end
  (Smt.unditto bs)

let boolify sq =
  let visitor = object (self : 'self)
  inherit [unit] Expr.Visit.map as super
  method hyp scx h = match h.core with
    | Defn (_, _, Hidden, _)    (** ignore these cases *)
    | Fact (_, Hidden, _) ->
        (adj scx h, h)
    | Fresh (nm, shp, lc, Bounded (r, rvis)) ->
        let dom = Bounded (nboo r, rvis) in
        let h = Fresh (nm, shp, lc, dom) @@ h in
        (adj scx h, h)
    | _ -> super#hyp scx h
  method expr scx e =
    eboo e
  method bounds scx bs =
    let bs = List.map begin
      fun (v, k, dom) -> match dom with
        | Domain d -> (v, k, Domain (nboo d))
        | _ -> (v, k, dom)
    end bs in
    let hs = List.map begin
      fun (v, k, _) -> Fresh (v, Shape_expr, k, Unbounded) @@ v
    end bs in
    let scx = adjs scx hs in
    (scx, bs)
  method exspec scx (trail, res) =
    let do_trail = function
      | Except_dot s -> Except_dot s
      | Except_apply e -> Except_apply (nboo e)
    in
    (List.map do_trail trail, nboo res)
  end in
  snd (visitor#sequent ((),sq.context) sq)
