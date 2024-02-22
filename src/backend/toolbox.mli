(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

val is_stopped: unit -> bool
(** Look in standard input for a STOP instruction from the toolbox, return
    true iff this instruction was received.
*)
val get_kills: unit -> int list
(** Look in standard input for KILL instructions from the toolbox, return
    the list of corresponding task numbers.
*)

(* backend/isabelle.ml *)
val toolbox_print:
  Proof.T.obligation ->
  ?temp:bool ->
  string ->
  string option ->
  string option ->
  float ->
  bool option ->
  bool ->
  Types.reason option ->
  string ->
  float option ->
    unit


(* backend/prep.ml *)
val print_new_res:
  Proof.T.obligation -> Types.status_type6 ->
  string -> float option -> unit
val print_message: string -> unit
val print_old_res:
    Proof.T.obligation -> Types.status_type6 ->
    bool -> unit

(* tlapm.ml *)
val print_ob_number: int -> unit
val print_message_url:
    string -> string -> unit

(* lsp *)
val normalize : bool -> Proof.T.obligation -> Proof.T.obligation
