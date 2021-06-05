(* Mint fresh TLA+ identifiers. *)
open Util


val mint_from_hint:
    hint -> hint
val mint_by_min_free:
    string -> int -> string list ->
        string
val mint_by_count:
    string -> int -> int * string
