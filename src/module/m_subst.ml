(* Utilities for performing substitutions in module syntax graphs. *)
open Property

open Expr.T
open Expr.Subst

open M_t


let rec app_modunits (s: sub) (mus: modunit list):  (sub * modunit list) =
    match mus with
  | [] -> (s, [])
  | (mu: modunit) :: mus ->
      let (s, (mu: modunit)) = app_modunit s mu in
      let (s, mus) = app_modunits s mus in
      (s, mu :: mus)


and app_modunit (s: sub) (mu: modunit):  (sub * modunit) =
  match mu.core with
  | Constants cs ->
      (bumpn (List.length cs) s, mu)
  | Recursives cs ->
      (bumpn (List.length cs) s, mu)
  | Variables vs ->
      (bumpn (List.length vs) s, mu)
  | Definition (df, wd, vis, ex) ->
      let df = app_defn s df in
      (bump s, Definition (df, wd, vis, ex) @@ mu)
  | Axiom (nm, e) ->
      let e = app_expr s e in
      let s = bumpn (if nm = None then 1 else 2) s in
      (s, Axiom (nm, e) @@ mu)
  | Theorem (nm, sq, naxs, prf, prf_orig,summ) ->
      let sq = app_sequent s sq in
      let s = bump s in
      let prf =
        let s = bumpn (Deque.size sq.context) s in
        Proof.Subst.app_proof s prf
      in
      let s = if nm = None then s else bump s in
      (s, Theorem (nm, sq, naxs, prf, prf_orig, summ) @@ mu)
  | Submod m ->
      let m = app_mule s m in
      (s, Submod m @@ mu)
  | Mutate (uh, us) ->
      let us = Proof.Subst.app_usable s us in
      let s = if uh = `Hide then s else bumpn (List.length us.facts) s in
      (s, Mutate (uh, us) @@ mu)
  | Anoninst (inst, loc) ->
      let isub = List.map (fun (v, e) -> (v, app_expr s e)) inst.inst_sub in
      (s, Anoninst ({inst with inst_sub = isub}, loc) @@ mu)


and app_mule (s: sub) (m: mule) =
  let (_, bod) = app_modunits s m.core.body in
  { m.core with body = bod } @@ m
