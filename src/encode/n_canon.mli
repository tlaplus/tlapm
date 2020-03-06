(*
 * encode/canon.mli --- eliminate primitives and builtins
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open Type.T

type gtx = ty_kind Ctx.t
type ltx = ty_kind Ctx.t

val expr : gtx -> ltx -> expr -> expr * ty
val sequent : gtx -> sequent -> gtx * sequent
val defn : gtx -> ltx -> defn -> defn
val defns : gtx -> ltx -> defn list -> ltx * defn list
val bound : gtx -> ltx -> bound -> bound
val bounds : gtx -> ltx -> bound list -> ltx * bound list
val hyp : gtx -> hyp -> hyp
val hyps : gtx -> hyp Deque.dq -> gtx * hyp Deque.dq
