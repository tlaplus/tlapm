(*
 * module/m_elab.mli --- module elaboration
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)
open Deque
open Expr.T
open Expr.Visit

open M_t


val normalize:
    modctx -> Expr.T.ctx -> mule ->
        modctx * mule * summary
