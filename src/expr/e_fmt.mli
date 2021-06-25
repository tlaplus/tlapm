(* Formatting of expressions.

Copyright (C) 2008-2010  INRIA and Microsoft Corporation
*)
open Tla_parser
open E_t
open Ctx


type ctx = hyp Deque.dq * int Ctx.ctx
val bump : ctx -> ctx

val adj : ctx -> Util.hint -> ctx * string
val adjs : ctx -> Util.hint list -> ctx * string list

val fmt_expr : ?temp:bool -> ctx -> expr -> Fu.exp

val fmt_bounds :
  ctx -> bound list -> ctx * (Format.formatter -> unit)
val extend_bound :
  ?prevdom:expr option ->
  ctx -> bound -> ctx * (string * expr option)
val extend_bounds :
  ?prevdom:expr option ->
  ctx -> bound list -> ctx * (string * expr option) list

val pp_print_shape : Format.formatter -> shape -> unit

val pp_print_bound :
  ctx -> Format.formatter -> string * expr option -> unit
val pp_print_expr : ?temp:bool ->  ctx -> Format.formatter -> expr -> unit
val pp_print_sel : ctx -> Format.formatter -> sel -> unit
val pp_print_defn : ctx -> Format.formatter -> defn -> ctx
val pp_print_defns : ctx -> Format.formatter -> defn list -> ctx
val pp_print_sequent : ?temp:bool -> ctx -> Format.formatter -> sequent -> ctx
val pp_print_hyp : ?temp:bool -> ctx -> Format.formatter -> hyp -> ctx
val pp_print_instance : ctx -> Format.formatter -> instance -> unit

val string_of_expr : hyp Deque.dq  -> expr -> string
