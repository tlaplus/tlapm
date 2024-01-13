(** Here we maintain the obligation info reveived from the parser.
    We try to make some evaluations lazy to make the parsing part faster. *)

type t

val make : Tlapm_lib.Proof.T.obligation option -> t
val text_plain : t -> string option
val text_normalized : t -> string option
val type_str : t -> string
