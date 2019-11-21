(*
 * proof/subst.ml --- proofs (substitution)
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev$";;

open Ext

open Property

open Expr.T
open Expr.Subst

open P_t

let rec app_proof s prf =
  { prf with core = app_proof_ s prf.core }

and app_proof_ s p =
  match p with
  | By (us, onl) -> By (app_usable s us, onl)
  | Obvious -> p
  | Steps (inits, qed) ->
      let (s, inits) = app_inits s inits in
      let qed_prf = app_proof s (get_qed_proof qed) in
      Steps (inits, {qed with core = Qed qed_prf})
  | Omitted _ -> p
  | Error _ -> p

and app_inits s = function
  | [] -> (s, [])
  | stp :: is ->
      let (s, stp) = app_step s stp in
      let (s, is) = app_inits s is in
      (s, stp :: is)

and app_step s stp = match stp.core with
  | Forget k ->
      (s, Forget k @@ stp)
  | Hide us ->
      (s, Hide (app_usable s us) @@ stp)
  | Define dfs ->
      let (s, dfs) = app_defns s dfs in
      (s, Define dfs @@ stp)
  | Assert (sq, prf) ->
      let sq = app_sequent s sq in
      let s = bumpn 2 s in    (* definition + negated original goal *)
      let prf = app_proof (bumpn (Deque.size sq.context) s) prf in
      (s, Assert (sq, prf) @@ stp)
  | Suffices (sq, prf) ->
      let sq = app_sequent s sq in
      let s = bumpn 2 s in    (* definition + negated original goal *)
      let prf = app_proof s prf in
      (bumpn (Deque.size sq.context) s, Suffices (sq, prf) @@ stp)
  | Pcase (e, p) ->
      let s = bumpn 1 s in
      let e = app_expr s e in
      let s = bumpn 1 s in
      let p = app_proof s p in
      (s, Pcase (e, p) @@ stp)
  | Pick (bs, e, p) ->
      let p = app_proof (bumpn 3 s) p in
      let (s, bs) = app_bounds s bs in
      let e = app_expr s e in
      (s, Pick (bs, e, p) @@ stp)
  | Use (us, onl) ->
      (s, Use (app_usable s us, onl) @@ stp)
  | Have e ->
      (bumpn 1 s, Have (app_expr s e) @@ stp)
  | Take bs ->
      let (s, bs) = app_bounds s bs in
      (s, Take bs @@ stp)
  | Witness es ->
      let es = List.map (app_expr s) es in
      (s, Witness es @@ stp)

and app_usable s us =
  let app_def dw =
    { dw with core =
        match dw.core with
          | Dvar v -> Dvar v
          | Dx n -> begin
              match app_ix s (n @@ dw) with
                | {core = Ix n} -> Dx n
                | e ->
                    Errors.set dw "substitution produced bad definition";
                    Expr.Fmt.pp_print_expr (Deque.empty, Ctx.dot) Format.std_formatter e;
                    Printf.printf "\n%!";

                    Util.eprintf ~at:dw "substitution produced bad definition" ;
                    failwith "Proof.Subst.app_usable"
            end
    }
  in
  { facts = List.map (app_expr s) us.facts
  ; defs = List.map app_def us.defs }
