(*
 * Copyright (C) 2012  INRIA and Microsoft Corporation
 *)

(** Store revision information for source files. *)

val f : string -> unit;;
(** This function should be called as [Revision.f "$Rev$"] in every source
    file.  It will record the Subversion revision number. *)

val get : unit -> string;;
(** This function returns the greatest of the revision numbers recorded
    by [f]. *)

