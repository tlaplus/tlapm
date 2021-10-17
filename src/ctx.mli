(*
 * ctx.mli --- generic contexts
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

type 'a ctx
type ident = { rep : string ; salt : int }

val length : 'a ctx -> int
val index  : 'a ctx -> int -> ident * 'a option
val front  : 'a ctx -> ident
val top    : 'a ctx -> ident * 'a option

val map    : 'a ctx -> (int -> 'a -> 'b) -> 'b ctx
val alter  : 'a ctx -> int -> (ident -> 'a -> 'a) -> 'a ctx

val mem : string -> 'a ctx -> bool

val dot : 'a ctx
val adj : 'a ctx -> string -> 'a -> 'a ctx

val using : 'a ctx -> string -> 'a -> ('a ctx -> ident -> 'b) -> 'b

val bump : 'a ctx -> 'a ctx

val push : int ctx -> string -> int ctx

val find_dep : 'a ctx -> string -> ('a option * int) option
val find : 'a ctx -> string -> 'a option
val depth : 'a ctx -> string -> int option

val to_list : 'a ctx -> 'a list

val string_of_ident : ident -> string
val pp_print_ident : Format.formatter -> ident -> unit

val pp_print_ctx :
    (Format.formatter -> 'a -> unit) ->
    Format.formatter -> 'a ctx -> unit

type 'a t = 'a ctx
