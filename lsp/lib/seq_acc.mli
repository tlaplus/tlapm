(** Returns elements from a sequence [seq] one by one and also collects all the
    returned elements in a list [acc]. This value has mutable fields. *)

type 'a t

val make : 'a Seq.t -> 'a t
(** Create new taker/accumulator from a sequence. The sequence is assumed to be
    infinite. *)

val take : 'a t -> 'a
(** Take next element from the sequence. *)

val acc : 'a t -> 'a list
(** Return all the elements previously returned by [take]. *)
