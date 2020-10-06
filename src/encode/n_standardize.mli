(*
 * encode/standardize.mli
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open Type.T


(* {3 Context} *)

type cx = ty2 Ctx.t


(* {3 Main} *)

val expr : cx -> expr -> expr * ty0
val eopr : cx -> expr -> expr * ty2
val earg : cx -> expr -> expr * ty1

val bound : cx -> bound -> bound
val bounds : cx -> bound list -> cx * bound list

val defn : cx -> defn -> cx * defn
val defns : cx -> defn list -> cx * defn list

val hyp : cx -> hyp -> cx * hyp
val hyps : cx -> hyp Deque.dq -> cx * hyp Deque.dq

val sequent : cx -> sequent -> sequent

val main : sequent -> sequent

