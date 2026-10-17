(** Generic contexts.

    Maintains a stack of names, resembling the stack with de-Bruijn indexes, and
    produces unique names in the case of overlapping identifier.

    Copyright (C) 2008-2010 INRIA and Microsoft Corporation *)
type 'a ctx

type ident
(** Stands for an identifier. Used to resolve name clashes by appending a number
    suffix. *)

val length: 'a ctx -> int
(** Current size of the stack/context. *)

val index: 'a ctx -> int -> ident * 'a option
(** Get the stack frame by index, position from the oldest element, 1-based. *)

val front: 'a ctx -> ident
(** Latest pushed identified in the stack. Same as [top], but no value is
    returned. *)

val top: 'a ctx -> ident * 'a option
(** Latest pushed element in the stack. *)

val map: 'a ctx -> (int -> 'a -> 'b) -> 'b ctx
(** Update all values in the context. The entries with no values assigned are
    left unchanged. *)

val alter:
    'a ctx -> int ->
    (ident -> 'a -> 'a) -> 'a ctx
(** [alter cx n f] updates element at position [n] in the context [cx] by
    applying function [f]. *)

val mem: string -> 'a ctx -> bool
(** Do we have name (not considering numbered suffix) in the context? *)

val dot: 'a ctx
(** Empty/fresh context.*)

val adj: 'a ctx -> string -> 'a -> 'a ctx
(** Push new name/value to the context. Don't know, why is it called [adj], for
    adjust? *)

val using:
    'a ctx -> string ->
    'a -> ('a ctx -> ident -> 'b) -> 'b
(** [using cx name value f] pushes new name/value to the stack and then invokes
    [f] on it. The function [f] gets the updated context and the identifier just
    created. *)

val bump: 'a ctx -> 'a ctx
(** Increases the context/stack with an unnamed element (named "") and no value
    attached. This produces names like [_7]. *)

val push: int ctx -> string -> int ctx
(** Pushes a name to the context. The value associated is the position of the
    pushed name in the stack (from the beginning). *)

val find_dep:
    'a ctx -> string ->
        ('a option * int) option
(** Finds the value associated with the latest identifier by a base name and
    returns how deep it is, if found. *)

val find: 'a ctx -> string -> 'a option
(** [find cx name] is the same as [find_dep cx name], just the depth is not
    returned. *)

val depth: 'a ctx -> string -> int option
(** [depth cx name] is the same as [find_dep cx name], just the value is not
    returned. *)

val to_list: 'a ctx -> 'a list
(** [to_list cx] will return a list of values pushed to the context. The values
    returned with the oldest value in the front. It will fail, there exist any
    entry in the context with no value associated. *)

val with_try_print_src : 'a ctx -> 'a ctx
(** To print the opaque elements without ? appended to them. *)

val try_print_src : 'a ctx -> bool
(** Was the [try_print_src] flag set? *)

val string_of_ident: ident -> string
(** Returns the disambiguated name of the identifier, i.e. either [name] or
    [name_x]. *)

val pp_print_ident:
    Format.formatter -> ident -> unit
(** Prints internal representation of the identifier. It is different from
    [string_of_indent]. *)

val pp_print_ctx:
    (Format.formatter -> 'a -> unit) ->
    Format.formatter -> 'a ctx -> unit
(** Print the current context. *)

type 'a t = 'a ctx [@@deriving show]
(** TODO: Should all other modules use ['a t] instead of ['a ctx]? It would
    follow the convention better. *)