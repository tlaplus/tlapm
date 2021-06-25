(*
 * prf/prep.ml --- ship obligations
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** Ship obligations to the backend *)

open Proof.T
open Types


val make_task :
  out_channel ->
  out_channel ->
  (bool -> obligation -> unit) ->
  obligation ->
    Schedule.task
(** @raise Exit if the toolbox sent the "stop" command. *)


val expand_defs : ?what:(Expr.T.wheredef -> bool) -> obligation -> obligation

(*
val normalize :
    obligation ->
    expand_enabled: bool ->
    expand_cdot: bool ->
    auto_expand_defs: bool ->
        obligation
*)
