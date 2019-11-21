(*
 * proof/fmt.mli --- proofs (pretty printing)
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ctx

open P_t

val pp_print_obligation : Format.formatter -> obligation -> unit
val pp_print_proof : Expr.Fmt.ctx -> Format.formatter -> proof -> unit
val pp_print_step : Expr.Fmt.ctx -> Format.formatter -> step -> Expr.Fmt.ctx
val pp_print_usable : Expr.Fmt.ctx -> Format.formatter -> usable -> unit

val string_of_step : Expr.T.hyp Deque.dq  -> step -> string
