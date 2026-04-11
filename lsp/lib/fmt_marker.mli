type 'a t
type 'a entry = private { value : 'a; from : int; till : int option }

val setup : Format.formatter -> (Format.stag -> (int * 'a) option) -> 'a t
val captured : 'a t -> 'a entry list
