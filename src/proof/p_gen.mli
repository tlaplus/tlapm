(*
 * proof/gen.mli --- generating proof obligations
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** Generating proof obligations *)

open Deque
open Property

open Expr.T

open P_t

(* val apply_defs : sequent -> sequent *)

val prove_assertion :
  suffices:bool ->
  hyp dq -> expr -> sequent wrapped -> time -> hyp dq * expr * time

val use_assertion :
  suffices:bool ->
  hyp dq -> expr -> sequent wrapped -> time -> hyp dq * expr

val get_steps_proof : proof -> step list

val generate : sequent -> proof -> time -> proof
val collect  : proof -> obligation list * proof

val mutate : hyp Deque.dq ->
  [`Use of bool | `Hide] -> usable wrapped -> time -> hyp Deque.dq * obligation list

type stats = {
  total      : int ;
  checked    : int ;
  absent     : Loc.locus list ;
  omitted    : Loc.locus list ;
  suppressed : Loc.locus list ;
}
val get_stats   : unit -> stats
val reset_stats : unit -> unit
