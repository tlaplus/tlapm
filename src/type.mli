(*
 * Copyright (C) 2012  INRIA and Microsoft Corporation
 *)

(** Packaging Module for TLA+'s Type System *)


(** Interface for the type and the constraint system *)
module T : sig
  open Util
  open Property

  type ty =
    | TUnknown
    | TVar of string
    | TAtom of ty_atom
    | TSet of ty
    | TArrow of ty * ty
    | TProd of ty list
  and ty_atom =
    | TU | TBool | TInt | TReal | TStr
  and ty_kind =
    | TKind of ty_kind list * ty

  module Sm = Coll.Sm
  type tmap = ty Sm.t

  val ord : ty_kind -> int

  val ty_u    : ty
  val ty_bool : ty
  val ty_int  : ty
  val ty_real : ty
  val ty_str  : ty

  val mk_atom_ty  : ty_atom -> ty
  val mk_kind_ty  : ty_kind list -> ty -> ty_kind
  val mk_cstk_ty  : ty -> ty_kind
  val mk_fstk_ty  : ty list -> ty -> ty_kind

  val get_atom  : ty -> ty_atom
  val get_ty    : ty_kind -> ty

  val get_atoms : ty -> ty_atom list

  val pp_print_type : Format.formatter -> ty -> unit
  val pp_print_kind : Format.formatter -> ty_kind -> unit

  module Props : sig
    val type_prop : ty pfuncs
    val atom_prop : ty_atom pfuncs
    val kind_prop : ty_kind pfuncs
  end

  val annot_type : hint -> ty -> hint
  val annot_sort : hint -> ty_atom -> hint
  val annot_kind : hint -> ty_kind -> hint

  val has_type : hint -> bool
  val has_sort : hint -> bool
  val has_kind : hint -> bool

  val get_type : hint -> ty
  val get_sort : hint -> ty_atom
  val get_kind : hint -> ty_kind
end

module Disambiguation : sig
  val cast_nm : T.ty_atom -> T.ty_atom -> string
  val z_plus      : string
  val z_minus     : string
  val z_uminus    : string
  val z_times     : string
  val z_quotient  : string
  val z_remainder : string
  val z_exp       : string
  val z_lteq      : string
  val z_lt        : string
  val z_gteq      : string
  val z_gt        : string
  val z_range     : string
  val r_plus      : string
  val r_minus     : string
  val r_uminus    : string
  val r_times     : string
  val r_ratio     : string
  val r_quotient  : string
  val r_remainder : string
  val r_exp       : string
  val r_lteq      : string
  val r_lt        : string
  val r_gteq      : string
  val r_gt        : string
  val r_range     : string
  val u_any : string
  val z_any : string
  val r_any : string
  val s_any : string
  val min_reconstruct : Expr.T.sequent -> Expr.T.sequent
end

