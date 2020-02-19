(*
 * reduce/nt_axioms.mli --- axioms for notypes encoding
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open Type.T

val uany_nm : string
val stringany_nm : string
val mem_nm : string
val subseteq_nm : string
val empty_nm : string
val enum_nm : int -> string
val union_nm : string
val power_nm : string
val cup_nm : string
val cap_nm : string
val setminus_nm : string
val setst_nm : string -> ty_kind -> string
(*val setof_nm : string -> ty_kind -> string*)
val boolean_nm : string
val booltou_nm : string
val string_nm : string
val stringtou_nm : string
val stringlit_nm : string -> string

val uany_decl : hyp
val stringany_decl : hyp
val mem_decl : hyp
val subseteq_decl : hyp
val empty_decl : hyp
val enum_decl : int -> hyp
val union_decl : hyp
val power_decl : hyp
val cup_decl : hyp
val cap_decl : hyp
val setminus_decl : hyp
val setst_decl : string -> ty_kind -> hyp
(*val setof_decl : string -> ty_kind -> hyp*)
val boolean_decl : hyp
val booltou_decl : hyp
val string_decl : hyp
val stringtou_decl : hyp
val stringlit_decl : string -> hyp

