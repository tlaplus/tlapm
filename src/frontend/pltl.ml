(*
 * frontend/pltl.ml
 *
 * The PLTL frontend expands definitions of [A]_v, <<A>>_v, \leadsto, WF and SF
 * (consider a version that does not expand the fairness predicates) and
 * coalesce all applications except those allowed in PLTL.

 * Copyright (C) 2013-2019  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev: 32093 $";;

open Ext
open Format
open Tla_parser
open Property

open Expr.T
open Proof.T
open Expr.Subst

module B = Builtin


let coalesce_fol =
  let visitor = object (self : 'self)
    inherit [unit] Expr.Visit.map as super
    method expr ((_, cx) as scx) e = begin match e.core with
      (* pltl expr are not changed *)
      | Apply ({ core = (
          Internal B.Conj
        | Internal B.Disj
        | Internal B.Implies
        | Internal B.Equiv
        | Internal B.TRUE
        | Internal B.FALSE
        | Internal B.Box _
        | Internal B.Diamond
        | Internal B.Prime
        | Internal B.Neg
      )}, _) -> super#expr scx e
      | Sequent _ -> super#expr scx e
      | List _ -> super#expr scx e
      |  Internal (
        B.Conj
        | B.Disj
        | B.Implies
        | B.Equiv
        | B.TRUE
        | B.FALSE
        | B.Box _
        | B.Diamond
        | B.Prime
        | B.Neg
      ) -> super#expr scx e
      | _ -> Coalesce.coalesce (snd scx) e
      end
  end in
  fun scx e ->
    visitor#expr scx e

let adj = Expr.Visit.adj

let box_assumptions =
  let visitor = object (self : 'self)
    inherit [unit] Expr.Visit.map as super
  method hyp scx h = match h.core with
  | Fact (e, Visible, Always) ->
    let h =
    Fact (Apply (Internal (B.Box true) @@ e, [self#expr scx e]) @@ e,
      Visible, Always) @@ h in
        (adj scx h, h)
  | _ -> super#hyp scx h
  end in
  fun scx e ->
    visitor#expr scx e


let expand_domains =
  let visitor = object (self : 'self)
    inherit [Expr.Subst.sub option] Expr.Visit.map as super
      method hyps (s, cx) hs = match Deque.front hs with
        | None -> ((s,cx), Deque.empty)
        | Some ({core = Fresh (nm, shp, lc, Bounded (r, rvis))} as h, hs) ->
          let s = match s with None -> shift 0 | Some s -> s in
          let h1 = Fresh (nm, shp, lc, Unbounded) @@ h in
          let cx = Deque.snoc cx h1 in
          let sr = app_expr (compose (shift 1) s) r in
          let s = bumpn 1 s in
          let e2 = Apply ((Internal B.Mem) @@ nm, [Ix 1 @@ nm ; sr]) @@ r in
          let tm = match lc with
            | Constant -> Expr.Temporal_props.compute_time cx r
            | _ -> Now in
          let h2 = Fact (e2, rvis, tm) @@ e2 in
          let cx = Deque.snoc cx h2 in
          let s = compose (shift 1) s in
          let (scx, hs) = self#hyps (Some s, cx) hs in
          (scx, Deque.cons h1 (Deque.cons h2 hs))
        | Some (h, hs) ->
          let ((s, cx), h) = self#hyp (s, cx) h in
          let s =
            match s with
            | None -> None
            | Some s -> Some (bump s)
          in
          let (scx, hs) = self#hyps (s, cx) hs in
          (scx, Deque.cons h hs)
      method expr (s, cx) e =
        match s with
        | None -> super#expr (s, cx) e
        | Some s -> super#expr (None, cx) (app_expr s e)
    end in
    fun (_, cx) e ->
      visitor#expr (None, cx) e

let process_eob ob =
  let cx = Deque.empty in
  let scx = ((), cx) in
  let ob = Coalesce.rename_with_loc cx ob in
  let ob = Expr.Tla_norm.expand_fairness scx ob in
  let ob = Expr.Tla_norm.expand_leadsto scx ob in
  let ob = Expr.Tla_norm.expand_action scx ob in
  let ob = expand_domains scx ob in
  let ob = box_assumptions scx ob in
  let ob = Expr.Levels.compute_level cx ob in
  let ob = Expr.SubstOp.compute_subst cx ob in
  let ob = coalesce_fol scx ob in
  ob

let process_obligation ob =
  match (process_eob (noprops (Sequent ob.obl.core))).core
  with
  | Sequent sq -> { ob with obl = { ob.obl with core = sq } }
  | _ -> failwith "Proof_prep.normalize"
