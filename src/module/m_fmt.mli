(*
 * mod/fmt.ml --- formatting
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** Formatting modules *)

open Ctx
open M_t


val pp_print_modunit:
    ?force:bool -> Expr.Fmt.ctx ->
        Format.formatter -> modunit -> Expr.Fmt.ctx
val pp_print_module:
    ?force:bool -> Expr.Fmt.ctx ->
        Format.formatter -> mule -> unit
val pp_print_modctx:
    Format.formatter -> modctx -> unit
val summary: mule -> unit
