(*
 * lazyList.mli --- lazy lists
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** Lazy lists *)

(** The type of lazy lists of objects of type ['a] *)
type +'a llist

type 'a t = 'a llist

type 'a front = Nil | Cons of 'a * 'a t

(** Note that all functions that have return type ['a t] create their
    output as lazily as possible. *)

(** eager *)
val expose : 'a llist -> 'a front

(** eager *)
val exact : 'a * 'a llist -> 'a llist

(** lazy *)
val delay : (unit -> 'a * 'a llist) -> 'a llist

(** {7 For convenience} *)

(** [empty] = [exact Nil] *)
val empty : 'a llist

(** [cons x ll] = [exact (Cons (x, l))] *)
val cons : 'a -> 'a llist -> 'a llist

(** {7 Operations} *)

(** eager *)
val length : 'a llist -> int

(** eager *)
val null : 'a llist -> bool

(** eager *)
val hd : 'a llist -> 'a

(** lazy *)
val tl : 'a llist -> 'a llist

(** eager *)
val take : int -> 'a llist -> 'a llist

(** lazy *)
val drop : int -> 'a llist -> 'a llist

(** lazy *)
val (@@) : 'a llist -> 'a llist -> 'a llist

(** lazy *)
val concat : 'a llist list -> 'a llist

(** lazy *)
val rev : 'a llist -> 'a llist

(** lazy *)
val map : ('a -> 'b) -> 'a llist -> 'b llist

(** lazy *)
val filter : ('a -> bool) -> 'a llist -> 'a llist

(** lazy *)
val filter_map : ('a -> 'b option) -> 'a llist -> 'b llist

(** eager *)
val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b llist -> 'a

(** eager *)
val fold_right : ('a -> 'b -> 'b) -> 'a llist -> 'b -> 'b

(** lazy *)
val unfold : 'a -> ('a -> ('b * 'a) option) -> 'b llist

(** {7 utilities} *)

(** lazy *)
val make : (unit -> 'a option) -> 'a llist
