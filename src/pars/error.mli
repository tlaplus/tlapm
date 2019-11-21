(*
 * error.mli --- errors
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** Errors *)

type error                          (** The abstract type of errors *)
type t = error                      (** convenience *)

(** Construct an error from the extents of a given dummy object. *)
val error : Loc.locus -> error

val err_combine : error -> error -> error
  (** unite two errors into a combined error *)

val err_add_message : string -> error -> error
  (** Add a new explanatory message. *)

val err_add_internal : string -> error -> error
  (** Add a new internal error message. *)

val err_add_expecting : string -> error -> error
  (** Add a new "expecting" message. *)

val err_set_unexpected : string -> error -> error
  (** Set the "unexpected" message (adding one if it doesn't exist) *)

(** Print the error on a given output channel. *)
val print_error : ?verbose:bool -> Pervasives.out_channel -> error -> unit

