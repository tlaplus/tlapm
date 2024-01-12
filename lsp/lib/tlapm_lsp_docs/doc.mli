(** Represents a document identified by its uri. It can contain multiple versions and all the related info. *)

type t

val make : Doc_vsn.t -> t
val add : t -> Doc_vsn.t -> t
val latest_vsn : t -> int
val set_actual_vsn : t -> int -> t option
val with_actual : t -> (t -> Doc_actual.t -> t * Doc_actual.t * 'a) -> t * 'a
val next_p_ref : t -> t * int
