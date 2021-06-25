(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

val print_warning: string -> unit
(* Send a "type:warning" message to the toolbox.
   Displays the message in a dialog box.
*)

val print_error: string -> string -> unit
(* [print_error msg url]
   Send a "type:error" message to the toolbox.
   Displays the message in a dialog box along with the (clickable) URL.
*)

val print_obligationsnumber: int -> unit
(* Send a "type:obligationsnumber" message to the toolbox. *)

val print_obligation:
    id: int ->
    loc: Loc.locus ->
    status: string ->
    fp: string option ->
    prover: string option ->
    meth: string option ->
    reason: string option ->
    already: bool option ->
    obl: string option ->
        unit
(* Send a "type:obligation" message to the toolbox. *)
