(*
 * type/simple.mli --- simple type reconstruction
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T

open T_t


(* {3 Context} *)

type ctx


(* {3 Main} *)

val main : sequent -> sequent

