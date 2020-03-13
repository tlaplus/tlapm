(*
 * reduce/nt_cook.mli
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open Type.T
open Property

type hyp_nm = string

val choose_nm : ty_kind -> expr -> string
val setst_nm : ty_kind -> expr -> string
val setof_nm : int -> ty_kind -> expr -> string
val fcn_nm : int -> ty_kind -> expr -> string
val choose_special_prop : (hyp_nm option * ty_kind * expr) pfuncs
val setst_special_prop : (hyp_nm option * ty_kind * expr) pfuncs
val setof_special_prop : (hyp_nm option * int * ty_kind * expr) pfuncs
val fcn_special_prop : (hyp_nm option * int * ty_kind * expr) pfuncs

val cook : sequent -> sequent
