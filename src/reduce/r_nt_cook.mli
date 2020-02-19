(*
 * reduce/nt_cook.mli
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open Type.T
open Property

val setst_nm : string -> string
val setst_prop : ty_kind pfuncs

val cook : sequent -> sequent
