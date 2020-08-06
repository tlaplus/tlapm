(*
 * encode/rewrite.mli --- rewrite sequents
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T

(** Bounds attached to variables (bound or declared) are eliminated
    and replaced by a guard.
*)
val simpl_bounds : sequent -> sequent

