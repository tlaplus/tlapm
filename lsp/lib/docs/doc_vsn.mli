(** Versions that are collected after the last prover launch or client asks for
    diagnostics. We store some limited number of versions here, just to cope
    with async events from the client. *)

type t

val make : string -> int -> t
val text : t -> string
val version : t -> int
val diff_pos : t -> t -> Range.Position.t
