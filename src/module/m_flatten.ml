(*
 * module/flatten.ml --- flatten modules (getting rid of EXTENDS)
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Property
open Util.Coll

open Expr.T
open Proof.T
open M_t

(*let debug = Printf.eprintf;;*)

let rec exports m =
  let rec spin body = function
    | [] -> List.rev body
    | mu :: mus -> begin match mu.core with
        | ( Constants _
          | Recursives _
          | Variables _
          | Axiom _
          | Anoninst _
          ) -> spin (mu :: body) mus
        | Definition (df, wd, vis, ex) ->
            let wd = if ex = Local then Builtin else wd in
            let mu = Definition (df, wd, vis, ex) @@ mu in
            spin (mu :: body) mus
        | Mutate _ ->
            spin body mus
        | Theorem (nm, sq, naxs, _, prf_orig, summ) ->
            let prf = Omitted (Elsewhere (Util.get_locus mu)) @@ mu in
            let mu = Theorem (nm, sq, naxs, prf, prf_orig, summ) @@ mu in
            spin (mu :: body) mus
        | Submod m ->
            let m = {m.core with body = exports m} @@ m in
            let mu = Submod m @@ mu in
            spin (mu :: body) mus
      end
  in match m.core.stage with
    | Final fin -> spin [] fin.final_named
    | _ -> spin [] m.core.body

let rec flatten (mcx : modctx) m seen =
  (*
   * preconditions:
   *
   * 1. all m.core.extendees are defined in mcx
   * 2. if any ex in m.core.extendees is final, it has defdepth 0
   *)
  assert (List.for_all (fun ex -> Sm.mem ex.core mcx) m.core.extendees);
  let (exbods, seen) =
    let f (acc, seen) ex =
      if Ss.mem ex.core seen then (acc, seen) else begin
        let exm = Sm.find ex.core mcx in
        let (exmf, seen) = flatten mcx exm seen in
        (exports exmf :: acc, Ss.add ex.core seen)
      end
    in
    List.fold_left f ([], seen) m.core.extendees
  in
  let extension = List.concat (List.rev exbods) in
  let m = {m.core with body = extension @ m.core.body} @@ m in
  (flatten_body mcx m, seen)

and flatten_body mcx m =
  let prefix = ref Deque.empty in
  let emit mu = prefix := Deque.snoc !prefix mu in
  let rec spin mcx = function
    | [] -> ()
    | mu :: mus -> begin match mu.core with
        | Submod m ->
            let (m, _) = flatten mcx m Ss.empty in
            let m = match m.core.stage with
              | Parsed | Flat -> { m.core with stage = Flat } @@ m
              | _ -> assert false
            in
            let m = { m.core with defdepth = Deque.size !prefix } @@ m in
            let mcx = Sm.add m.core.name.core m mcx in
            emit (Submod m @@ mu) ;
            spin mcx mus
        | _ ->
            emit mu ;
            spin mcx mus
      end
  in
  spin mcx m.core.body ;
  {m.core with body = Deque.to_list !prefix; stage = Flat} @@ m
;;
