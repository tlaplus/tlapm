(*
 * proof/simplify.mli --- simplify proofs
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** Simplify proofs *)

open Property
open Deque

open Expr.T

open P_t

val simplify : hyp dq -> expr -> proof -> time -> proof
