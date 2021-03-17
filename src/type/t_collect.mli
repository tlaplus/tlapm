(*
 * encode/coltypes.mli --- collect types in an expression
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open T_t

(** Collect all constant types (also called "sorts") found in an expression *)
val main : sequent -> Ts.t

