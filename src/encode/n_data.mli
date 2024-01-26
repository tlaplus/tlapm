(*
 * encode/data.mli --- symbol data
 *
 *
 * Copyright (C) 2022  INRIA and Microsoft Corporation
 *)

open Type.T

open N_table

type smb_kind = Untyped | Typed | Special

(** Basic information associated to a symbol *)
type data =
  { dat_name  : string
  ; dat_ty2   : ty2
  ; dat_kind  : smb_kind
  ; dat_tver  : tla_smb option
  }

(** Dependencies of a symbol (other symbols and axioms).
    The dependencies may depend on previous declarations in some cases.  For
    that reason, they are separated from the basic info, which is the same
    whatever the context.
*)
type dep_data =
  { dat_deps  : tla_smb list
  ; dat_axms  : tla_axm list
  }

val get_data : tla_smb -> data

type s
val init : s

val get_deps : solver:string -> disable_arithmetic:bool -> smt_set_extensionality:bool -> tla_smb -> s -> s * dep_data

