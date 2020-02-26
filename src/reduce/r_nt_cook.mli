(*
 * reduce/nt_cook.mli
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open Type.T
open Property

val setst_nm : ty_kind -> expr -> string
val setst_special_prop : (ty_kind * expr) pfuncs

val cook : sequent -> sequent
