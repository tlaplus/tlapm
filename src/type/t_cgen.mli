(*
 * type/cgen.mli --- constraint generation
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T

open T_t


(** [cgenerate sq] annotates [sq] with type variables and returns a
    constraint expression to solve.
*)
val cgenerate : sequent -> sequent * cstr

