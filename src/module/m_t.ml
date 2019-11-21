(*
 * module/t.ml --- modules
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev$";;

(** Modules *)

open Ext
open Property
open Util
open Coll

open Expr.T
open Proof.T

(** module type. Can't use "module" because it's a keyword in OCaml. *)
type mule = mule_ wrapped
and mule_ = {
  name              : hint ;
  extendees         : hint list ;
  instancees        : hint list ;
    (* only external instancees *)
  body              : modunit list ;
  defdepth          : int ;
  mutable stage     : stage ;
  mutable important : bool
}

(** module unit *)
and modunit = modunit_ wrapped
and modunit_ =
  | Constants  of (hint * shape) list
  | Recursives of (hint * shape) list
  | Variables  of hint list
  | Definition of defn * wheredef * visibility * export
  | Axiom      of hint option * expr
  | Theorem    of hint option * sequent * int * proof * proof * summary
  | Submod     of mule
  | Mutate     of [`Use of bool | `Hide] * usable
  | Anoninst   of instance * export

and named = Named | Anonymous

and summary = {
  sum_total      : int ;
  sum_absent     : int * Loc.locus list ;
  sum_omitted    : int * Loc.locus list ;
  sum_suppressed : int * Loc.locus list ;
}

and stage =
  | Special
  | Parsed | Flat
  | Final of final

and final = { final_named  : modunit list
            ; final_obs    : obligation array
            ; final_status : status * summary
            }

and status =
  | Unchecked | Proved | Certified | Incomplete

(** module context *)
type modctx = mule Sm.t

let empty_summary = { sum_total      = 0
                    ; sum_absent     = (0, [])
                    ; sum_omitted    = (0, [])
                    ; sum_suppressed = (0, []) }

let cat_summary s t =
  let vcat (m, j) (n, l) = (m + n, j @ l) in
  { sum_total = s.sum_total + t.sum_total
  ; sum_absent = vcat s.sum_absent t.sum_absent
  ; sum_omitted = vcat s.sum_omitted t.sum_omitted
  ; sum_suppressed = vcat s.sum_suppressed t.sum_suppressed
  }

let salt_prop : unit pfuncs = Property.make "Module.salt_prop"

open Expr.Subst

let hyps_of_modunit (mu : modunit) = match mu.core with
  | Constants cs ->
      List.map (fun (nm, shp) ->
                  Fresh (nm, shp, Constant, Unbounded) @@ mu) cs
  | Recursives cs ->
      List.map (fun (nm, shp) ->
                  Defn (Recursive (nm, shp) @@ mu, User, Hidden, Export) @@ mu)
               cs
  | Variables vs ->
      List.map (fun nm -> Flex nm @@ mu) vs
  | Definition (df, wd, vis, ex) ->
      [ Defn (df, wd, vis, ex) @@ mu ]
  | Axiom (None, e) ->
      [ Fact (e, Hidden, Always) @@ mu ]
  | Axiom (Some nm, e) -> [
      Defn (Operator (nm, e) @@ mu, User, Visible, Export) @@ mu ;
      Fact (Ix 1 @@ mu, Hidden, Always) @@ mu ;
    ]
  | Theorem (nm, sq, naxs, _, _, _) -> begin
      let rec drop sq = function
        | 0 -> sq
        | n -> begin match Deque.front sq.context with
            | Some (_, cx) ->
                drop { sq with context = cx } (n - 1)
            | None -> Errors.bug ~at:mu "Module.hyps_of_modunit: naxs > #cx"
          end
      in
      let sq = app_sequent (shift (- naxs)) (drop sq naxs) in
      match nm with
        | None ->
            [ Fact (exprify_sequent sq @@ mu, Hidden, Always) @@ mu ]
        | Some nm -> [
            Defn (Operator (nm, exprify_sequent sq @@ nm) @@ mu,
                  User, Visible, Export) @@ mu ;
            Fact (Ix 1 @@ mu, Hidden, Always) @@ mu ;
          ]
    end
  | Mutate (`Use _, us) ->
      List.mapi begin
        fun n f -> Fact (app_expr (shift n) f, Visible, Always) @@ mu
      end us.facts
  | Submod _
  | Mutate _
  | Anoninst _ -> []

let hyp_size (mu : modunit) = match mu.core with
  | Constants cs -> List.length cs
  | Recursives cs -> List.length cs
  | Variables vs -> List.length vs
  | Definition _ -> 1
  | Axiom (nm, _)
  | Theorem (nm, _, _, _, _, _) -> if nm = None then 1 else 2
  | Mutate (`Use _, us) -> List.length us.facts
  | Submod _
  | Mutate _
  | Anoninst _ -> 0
