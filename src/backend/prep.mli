(* Preparation of proof obligations, and calls to backends.

Copyright (C) 2008-2010  INRIA and Microsoft Corporation
*)
open Proof.T
open Types


(** Ship proof obligations to the backend *)
val make_task:
  out_channel ->
  out_channel ->
  (bool -> obligation -> unit) ->
  obligation ->
    Schedule.task
  (** @raise Exit if the toolbox sent the "stop" command. *)


val expand_defs:
    ?what:(Expr.T.wheredef -> bool) ->
    obligation -> obligation

(*
val normalize:
    obligation ->
    expand_enabled: bool ->
    expand_cdot: bool ->
    auto_expand_defs: bool ->
        obligation
*)

val prepare_obligation: obligation -> obligation
