type t = private { decomposition_disj_cases : bool }
(** Configuration of the LSP server. The values are received from the LSP
    client, currently on init, but later updates can be added as well. *)

val default : t
val set_decomposition_disj_cases : bool -> t -> t
