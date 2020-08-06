(*
 * encode/rewrite.ml --- rewrite sequents
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T

open Property

module Subst = Expr.Subst
module Visit = Expr.Visit
module B = Builtin


let error ?at mssg =
  let mssg = "Encode.Rewrite: " ^ mssg in
  Errors.bug ?at mssg


let simpl_bounds_visitor = object (self : 'self)
  inherit [unit] Visit.map as super

  (* TODO preserve type info *)

  method expr scx oe =
    match oe.core with

    | Quant (q, bs, e) ->
        let n = List.length bs in
        let scx, rbs, hs, dit, _ =
          List.fold_left begin fun (nscx, rbs, hs, dit, i) (v, k, d) ->
            let h = Fresh (v, Shape_expr, k, Unbounded) %% [] in
            let nscx = Visit.adj scx h in
            let b = (v, k, No_domain) in
            match d, dit with
            | No_domain, _ ->
                (nscx, b :: rbs, hs, None, i - 1)
            | Domain d, _ ->
                let d = self#expr scx d in
                let d = Subst.app_expr (Subst.shift n) d in
                let h =
                  Apply (Internal B.Mem %% [], [
                    Ix i %% [] ; d
                  ]) %% []
                in
                (nscx, b :: rbs, h :: hs, Some d, i - 1)
            | Ditto, Some d ->
                let h =
                  Apply (Internal B.Mem %% [], [
                    Ix i %% [] ; d
                  ]) %% []
                in
                (nscx, b :: rbs, h :: hs, Some d, i - 1)
            | _, _ ->
                error ~at:oe "Missing bound"
          end (scx, [], [], None, n) bs
        in
        let bs = List.rev rbs in
        let hs = List.rev hs in
        let e = self#expr scx e in
        let e =
          match hs, q with
          | [], _ -> e
          | [h], Forall ->
              Apply (Internal B.Implies %% [], [
                h ; e
              ]) %% []
          | _, Forall ->
              Apply (Internal B.Implies %% [], [
                List (And, hs) %% [] ; e
              ]) %% []
          | _, Exists ->
              List (And, hs @ [ e ]) %% []
        in
        Quant (q, bs, e) @@ oe

    | Choose (v, Some d, e) ->
        let d = self#expr scx d in
        let h = Fresh (v, Shape_expr, Constant, Unbounded) %% [] in
        let scx = Visit.adj scx h in
        let e = self#expr scx e in
        let e =
          Apply (Internal B.Conj %% [], [
            Apply (Internal B.Mem %% [], [
              Ix 1 %% [] ; Subst.app_expr (Subst.shift 1) d
            ]) %% [] ;
            e
          ]) %% []
        in
        Choose (v, None, e) @@ oe

    | _ -> super#expr scx oe

  (* NOTE method hyps is ignored, because a substitution must be built across the context
   * and applied to each hyp and the succedent.  This substitution renames variables to
   * account for new hypotheses in the context. *)
  method sequent scx sq =
    let rec spin scx sub hs =
      match Deque.front hs with
      | None -> (scx, sub, Deque.empty)

      | Some ({ core = Fresh (v, shp, k, Bounded (d, vis)) } as h, hs) ->
          let d = Subst.app_expr sub d in
          let d = self#expr scx d in
          let h = Fresh (v, shp, k, Unbounded) @@ h in
          let hh =
            Fact (
              Apply (Internal B.Mem %% [], [
                Ix 1 %% [] ; Subst.app_expr (Subst.shift 1) d
              ]) %% [],
              vis, NotSet
            ) %% []
          in
          let scx = Visit.adj scx h in
          let sub = Subst.bump sub in
          let scx = Visit.adj scx hh in
          let sub = Subst.compose (Subst.shift 1) sub in
          let scx, sub, hs = spin scx sub hs in
          (scx, sub, Deque.cons h (Deque.cons hh hs))

      | Some (h, hs) ->
          let h = Subst.app_hyp sub h in
          let scx, h = self#hyp scx h in
          let sub = Subst.bump sub in
          let scx, sub, hs = spin scx sub hs in
          (scx, sub, Deque.cons h hs)
    in
    let scx, sub, hs = spin scx (Subst.shift 0) sq.context in
    let e = Subst.app_expr sub sq.active in
    let e = self#expr scx e in
    (scx, { context = hs ; active = e })
end

let simpl_bounds sq =
  let cx = ((), Deque.empty) in
  snd (simpl_bounds_visitor#sequent cx sq)


let simpl_elims_visitor = object (self : 'self)
  inherit [unit] Visit.map as super

  method expr scx oe =
    match oe.core with
    | Apply ({ core = Internal B.Notmem } as op, [ e ; f ]) ->
        let e = self#expr scx e in
        let f = self#expr scx f in
        Apply (Internal B.Neg %% [], [
          Apply (Internal B.Mem @@ op, [ e ; f ]) %% []
        ]) @@ oe
    | _ -> super#expr scx oe
end

let simpl_elims sq =
  let cx = ((), Deque.empty) in
  snd (simpl_elims_visitor#sequent cx sq)

