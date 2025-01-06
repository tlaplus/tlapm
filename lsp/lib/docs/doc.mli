(** Represents a document identified by its uri. It can contain multiple
    versions and all the related info. *)

open Util

type t

val make : LspT.DocumentUri.t -> Doc_vsn.t -> Util.parser_fun -> t
val with_parser : t -> Util.parser_fun -> t
val add : t -> Doc_vsn.t -> t
val latest_vsn : t -> int
val set_actual_vsn : t -> int -> t option
val with_actual : t -> (t -> Doc_actual.t -> t * Doc_actual.t * 'a) -> t * 'a
