(*
 * encode/table.mli --- table of symbols used to encode POs
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Type.T


(* {3 Symbols} *)

type family =
  | Logic
  | Sets
  | Booleans
  | Strings
  | Tuples
  | Functions
  | Records
  | Sequences
  | Arithmetic
  | Special

type smb

val mk_smb : family -> string -> ty_kind -> smb
val mk_cst_smb : family -> string -> ty -> smb
val mk_fst_smb : family -> string -> ty list -> ty -> smb
val mk_snd_smb : family -> string -> (ty list * ty) list -> ty -> smb

val get_fam  : smb -> family
val get_name : smb -> string
val get_kind : smb -> ty_kind
val get_ord  : smb -> int

val u_kind : ty_kind -> ty_kind
val u_smb : smb -> smb


(* {3 Table} *)

val choose : ty -> smb

val mem : ty -> smb
val subseteq : ty -> smb
val setenum : int -> ty -> smb
val union : ty -> smb
val subset : ty -> smb
val cup : ty -> smb
val cap : ty -> smb
val setminus : ty -> smb
val setst : ty -> smb
val setof : ty list -> ty -> smb

val set_boolean : smb
val set_string : smb
val set_int : smb
val set_nat : smb
val set_real : smb

val arrow : ty -> ty -> smb
val domain : ty -> ty -> smb
val fcnapp : ty -> ty -> smb
val fcn : ty -> ty -> smb
val except : ty -> ty -> smb

val product : ty list -> smb
val tuple : ty list -> smb
