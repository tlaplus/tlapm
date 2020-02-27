(*
 * reduce/nt_cook.ml
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open Type.T
open Property
open Util.Coll

module A = R_nt_axioms
module B = Builtin


type hyp_nm = string

let scount = ref 0
let get_scount () =
  scount := !scount + 1;
  !scount

let setst_nm _ _ = "cooked_" ^ string_of_int (get_scount ())

let setst_special_prop = make "Reduce.Cook.setst_special_prop"


(* {3 Mark Global Variables} *)

let is_global_prop = make "Reduce.Cook.is_global_prop"

let mark_global = object (self : 'self)
  inherit [unit] Expr.Visit.map as super

  method expr _ oe = oe (* Gain some time *)

  method hyp scx h =
    match h.core with
    | Fresh (nm, shp, lc, dom) ->
        let nm = assign nm is_global_prop () in
        let h = Fresh (nm, shp, lc, dom) @@ h in
        (Expr.Visit.adj scx h, h)
    | Flex s ->
        let s = assign s is_global_prop () in
        let h = Flex s @@ h in
        (Expr.Visit.adj scx h, h)
    | Defn (df, wd, vis, ex) ->
        let df =
          match df.core with
          | Recursive (nm, shp) ->
              let nm = assign nm is_global_prop () in
              Recursive (nm, shp) @@ df
          | Operator (nm, e) ->
              let nm = assign nm is_global_prop () in
              Operator (nm, e) @@ df
          | Instance (nm, i) ->
              let nm = assign nm is_global_prop () in
              Instance (nm, i) @@ df
          | Bpragma (nm, e, l) ->
              let nm = assign nm is_global_prop () in
              Bpragma (nm, e, l) @@ df
        in
        let h = Defn (df, wd, vis, ex) @@ h in
        (Expr.Visit.adj scx h, h)
    | Fact (e, vis, tm) ->
        let h = Fact (e, vis, tm) @@ h in
        (Expr.Visit.adj scx h, h)
end


(* {3 Main} *)

let split_global_local (_, hx) xs =
  Expr.Collect.vs_partition hx begin fun _ h ->
    let nm = hyp_hint h in
    has nm is_global_prop
  end xs

let globally_bound scx xs =
  fst (split_global_local scx xs)

let locally_bound scx xs =
  snd (split_global_local scx xs)

let hyp_sort hx ix =
  let h = (get_val_from_id hx ix) in
  get_sort (hyp_hint h)

let visitor = object (self : 'self)
  inherit [unit] Expr.Visit.map as super

  method expr scx oe =
    match oe.core with
    | SetSt (h, e1, e2) ->
        let e1 = self#expr scx e1 in
        let hyp = Fresh (h, Shape_expr, Constant, Bounded (e1, Visible)) @@ h in
        let (_, hx as scx) = Expr.Visit.adj scx hyp in
        let e2 = self#expr scx e2 in

        let ys = Expr.Collect.fvs ~ctx:(Deque.snoc Deque.empty hyp) e2 in
        let gs, ys = split_global_local scx ys in
        let ys = Is.elements ys in

        let min = Is.min_elt gs in
        let nm = hyp_name (get_val_from_id hx min) in

        let ins = List.map (hyp_sort hx) ys in
        let k = mk_fstk_ty (ty_u :: List.map mk_atom_ty ins) ty_u in
        let s = setst_nm k e2 in
        let op = assign (Opaque s %% []) setst_special_prop (Some nm, k, e2) in
        Apply (op, e1 :: List.map (fun i -> Ix i %% []) ys) @@ oe

    | _ -> super#expr scx oe
end

let cook sq =
  let _, sq = mark_global#sequent ((), Deque.empty) sq in
  let _, sq = visitor#sequent ((), Deque.empty) sq in
  sq
