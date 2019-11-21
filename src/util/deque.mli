(*
 * deque.ml --- Persistent functional double-ended queues
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

type 'a dq

val empty : 'a dq
val size  : 'a dq -> int
val cons  : 'a -> 'a dq -> 'a dq
val snoc  : 'a dq -> 'a -> 'a dq
val front : 'a dq -> ('a * 'a dq) option
val rear  : 'a dq -> ('a dq * 'a) option
val rev   : 'a dq -> 'a dq
val null  : 'a dq -> bool
val nth   : ?backwards:bool -> 'a dq -> int -> 'a option
val map   : (int -> 'a -> 'b) -> 'a dq -> 'b dq
val iter  : (int -> 'a -> unit) -> 'a dq -> unit

val find  : ?backwards:bool -> 'a dq -> ('a -> bool) -> (int * 'a) option

val alter : ?backwards:bool -> 'a dq -> int -> ('a -> 'a) -> 'a dq

val fold_left  : ('acc -> 'a -> 'acc) -> 'acc -> 'a dq -> 'acc
val fold_right : ('a -> 'acc -> 'acc) -> 'a dq -> 'acc -> 'acc

val append       : 'a dq -> 'a dq -> 'a dq
val append_list  : 'a dq -> 'a list -> 'a dq
val prepend_list : 'a list -> 'a dq -> 'a dq

val of_list : 'a list -> 'a dq
val to_list : 'a dq -> 'a list
