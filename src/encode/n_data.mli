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
  ; dat_deps  : tla_smb list
  ; dat_axms  : tla_axm list
  ; dat_kind  : smb_kind
  }

type s
(** Data for a symbol sometimes depends on the data previously obtained.
    Examples: generating axioms to state for all declared strings are
    distinct from each other.
*)

val init : s
val get_data : s -> tla_smb -> s * data

(** Return the actual formula for an axiom.
    The result is a closed formula in standardized form (see
    {!Encode.Standardize}).
*)
val get_axm : tla_axm -> expr

