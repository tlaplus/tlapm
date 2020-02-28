(*
 * reduce/nt_cook.ml
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
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

let depth (_, hx) =
  Deque.find ~backwards:true hx (fun h -> has (hyp_hint h) is_global_prop)
  |> Ext.Option.get |> fst

(* Returns (hx1, hx2) where hx1 is global and hx2 local *)
let split_ctx hx =
  let rec spin l r =
    match Deque.rear l with
    | None ->
        (l, r)
    | Some (_, h) when has (hyp_hint h) is_global_prop ->
        (l, r)
    | Some (l, h) ->
        spin l (Deque.cons h r)
  in
  spin hx Deque.empty

let dummy = Opaque "error" %% []

(* Here be dragons *)
let badaboom n xs ?(sft1=0) ?(sft2=0) e =
  (* shft1: length of additional upper local ctx *)
  (* shft2: length of additional lower local ctx *)
  let j = ref 0 in
  let dq =
    List.fold_left begin fun dq i ->
      let k =
        if Is.mem i xs then
          begin j := !j + 1; Some (!j) end
        else
          None
      in
      Deque.snoc dq k
    end Deque.empty (List.init n (fun i -> i + 1))
  in
  let sub = Deque.fold_right begin function
    | None -> Expr.Subst.scons dummy
    | Some k -> Expr.Subst.scons (Ix (k + sft2) %% [])
  end dq (Expr.Subst.shift (Is.cardinal xs + sft1)) in
  Expr.Subst.app_expr sub e

let visitor = object (self : 'self)
  inherit [unit] Expr.Visit.map as super

  method expr (_, hx as scx) oe =
    match oe.core with
    | SetSt (h, e1, e2) ->
        let e1 = self#expr scx e1 in
        let hyp = Fresh (h, Shape_expr, Constant, Bounded (e1, Visible)) @@ h in
        let (_, hx' as scx') = Expr.Visit.adj scx hyp in
        (* distinct name for hx' bc we need to contextualise the final
         * expression in hx at the end *)
        let e2 = self#expr scx' e2 in

        let gx, lx = split_ctx hx' in
        let gsz = Deque.size gx in
        let lsz = Deque.size lx in

        let vs = Expr.Collect.fvs e2 in

        let lvs = locally_bound scx' vs in
        let lvs' = Is.add 1 lvs in
        let e2 = badaboom lsz lvs' ~sft1:1 e2 in (* Dark magic *)

        let lsz' = 1 + Is.cardinal lvs' in (* Size of new local ctx of e2 *)
        let _ = lsz' in

        Format.eprintf "SIZE OF G: %d@." gsz;
        Format.eprintf "SIZE OF L: %d@." lsz;
        Format.eprintf "SIZE OF L': %d@." lsz';

        (* shift global variables along skipped global ctx *)
        (* FIXME This part would not be necessary if the hypothesis was
         * simply inserted right above the local ctx. *)
        let gvs = Is.filter (fun i -> not (Is.mem i lvs)) vs in
        let nm, e2 =
          if Is.is_empty gvs then begin
            Format.eprintf "NO GVAR@.";
            None, e2
          end else begin
            let m = Is.min_elt gvs in
            let v = hyp_name (get_val_from_id gx (m - lsz)) in
            Format.eprintf "FIRST GVAR: %d:%s@." m v;
            let s = lsz - m + 1 in
            let sub = Expr.Subst.bumpn lsz' (Expr.Subst.shift s) in
            let e2 = Expr.Subst.app_expr sub e2 in
            Some v, e2
          end
        in

        let args = lvs
          |> Is.remove 1
          |> Is.elements
          |> List.map (fun i -> i - 1)
          |> List.rev
        in

        let ins = List.map (hyp_sort hx) args in
        let k = mk_fstk_ty (ty_u :: List.map mk_atom_ty ins) ty_u in
        let s = setst_nm k e2 in
        let op = assign (Opaque s %% []) setst_special_prop (nm, k, e2) in
        Apply (op, e1 :: List.map (fun i -> Ix i %% []) args) @@ oe

    | _ -> super#expr scx oe
end

let cook sq =
  let _, sq = mark_global#sequent ((), Deque.empty) sq in
  let _, sq = visitor#sequent ((), Deque.empty) sq in
  sq
