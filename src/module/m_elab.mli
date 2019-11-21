(*
 * mod/elab.ml --- elaboration
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** Elaborate modules *)

open Proof.T
open M_t

val normalize : modctx -> Expr.T.hyp Deque.dq -> mule -> modctx * mule * summary
