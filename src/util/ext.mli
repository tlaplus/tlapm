(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

module List : sig
  (* include List *)
  val length : 'a list -> int
  val hd : 'a list -> 'a
  val tl : 'a list -> 'a list
  val nth : 'a list -> int -> 'a
  val rev : 'a list -> 'a list
  val append : 'a list -> 'a list -> 'a list
  val rev_append : 'a list -> 'a list -> 'a list
  val concat : 'a list list -> 'a list
  val flatten : 'a list list -> 'a list
  val iter : ('a -> unit) -> 'a list -> unit
  val map : ('a -> 'b) -> 'a list -> 'b list
  val rev_map : ('a -> 'b) -> 'a list -> 'b list
  val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
  val fold_right : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val iter2 : ('a -> 'b -> unit) -> 'a list -> 'b list -> unit
  val map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  val rev_map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  val fold_left2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b list -> 'c list -> 'a
  val fold_right2 : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
  val for_all : ('a -> bool) -> 'a list -> bool
  val exists : ('a -> bool) -> 'a list -> bool
  val for_all2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
  val exists2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
  val mem : 'a -> 'a list -> bool
  val memq : 'a -> 'a list -> bool
  val find : ('a -> bool) -> 'a list -> 'a
  val filter : ('a -> bool) -> 'a list -> 'a list
  val find_all : ('a -> bool) -> 'a list -> 'a list
  val partition : ('a -> bool) -> 'a list -> 'a list * 'a list
  val assoc : 'a -> ('a * 'b) list -> 'b
  val assq : 'a -> ('a * 'b) list -> 'b
  val mem_assoc : 'a -> ('a * 'b) list -> bool
  val mem_assq : 'a -> ('a * 'b) list -> bool
  val remove_assoc : 'a -> ('a * 'b) list -> ('a * 'b) list
  val remove_assq : 'a -> ('a * 'b) list -> ('a * 'b) list
  val split : ('a * 'b) list -> 'a list * 'b list
  val combine : 'a list -> 'b list -> ('a * 'b) list
  (* val sort : ('a -> 'a -> int) -> 'a list -> 'a list *)
  val stable_sort : ('a -> 'a -> int) -> 'a list -> 'a list
  val fast_sort : ('a -> 'a -> int) -> 'a list -> 'a list
  val merge : ('a -> 'a -> int) -> 'a list -> 'a list -> 'a list

  val unique : ?cmp:('a -> 'a -> bool) -> 'a list -> 'a list
  val init : int -> (int -> 'a) -> 'a list
  val mapi : (int -> 'e -> 'f) -> 'e list -> 'f list
  val filter_map : ('g -> 'h option) -> 'g list -> 'h list
  val find_exc : ('a -> bool) -> exn -> 'a list -> 'a
  val sort : ?cmp:('a -> 'a -> int) -> 'a list -> 'a list
  val iteri : (int -> 'a -> unit) -> 'a list -> unit
  val split_nth : int -> 'a list -> 'a list * 'a list
end;;

module Option : sig
  val get : 'a option -> 'a
  val map : ('a -> 'b) -> 'a option -> 'b option
  val iter : ('a -> unit) -> 'a option -> unit
  val default : 'a -> 'a option -> 'a
  val is_some : 'a option -> bool
  val is_none : 'a option -> bool
end;;

module Std : sig
  val unique : unit -> int
  val input_file : ?bin:bool -> string -> string
  val input_list : in_channel -> string list
  val input_all : ?bsize:int -> in_channel -> string
  val identity : 'a -> 'a
  val finally : (unit -> unit) -> ('a -> 'b) -> 'a -> 'b
end;;

val string_contains : string -> string -> bool
val is_prefix : string -> string -> bool
(** [starts_with prefix text]
    Return [true] if [prefix] is a prefix of [text] *)

val split : string -> char -> string list
(** [split text sep]
    Split the [text] at the occurrences of [sep] and return the resulting
    list of strings. *)
