(*
 * module/gen.mli --- generation of obligations
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Proof.T
open M_t


val generate:
    Expr.T.hyp Deque.dq -> mule ->
        mule * obligation list * summary
val collect_usables: mule -> usable option
