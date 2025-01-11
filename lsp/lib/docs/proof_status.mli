open Prover

type t = Proved | Failed | Omitted | Missing | Pending | Progress
[@@deriving show]

val of_tlapm_obl_state : Toolbox.tlapm_obl_state -> t
val to_string : t -> string
val to_message : t -> string
val to_order : t -> int
val of_order : int -> t
val bot : t
val top : t
val min : t -> t -> t
val max : t -> t -> t
val yojson_of_t : t -> Yojson.Safe.t

val is_diagnostic : t -> bool
(** Returns true, if this state should be shown as a diagnostic. *)
