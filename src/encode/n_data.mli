(*
 * encode/data.mli --- symbol data
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open Type.T

open N_table

type smb_kind = Untyped | Typed | Special

type data =
  { dat_name  : string
  ; dat_ty2   : ty2
  ; dat_kind  : smb_kind
  }

type dep_data =
  { dat_deps  : tla_smb list
  ; dat_axms  : tla_axm list
  }

val get_data : tla_smb -> data

type s
val init : s

val get_deps : tla_smb -> s -> s * dep_data

(** Return the actual formula for an axiom.
    The result is a closed formula in standardized form (see
    {!Encode.Standardize}).
*)
val get_axm : tla_axm -> expr

