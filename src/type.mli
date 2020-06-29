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

  val get_types : ty_kind -> ty list

  val ty_to_string : ty -> string

  val pp_print_type : Format.formatter -> ty -> unit
  val pp_print_kind : Format.formatter -> ty_kind -> unit

  module Props : sig
    val type_prop : ty pfuncs
    val atom_prop : ty_atom pfuncs
    val kind_prop : ty_kind pfuncs
  end

  val annot_type : 'a wrapped -> ty -> 'a wrapped
  val annot_sort : 'a wrapped -> ty_atom -> 'a wrapped
  val annot_kind : 'a wrapped -> ty_kind -> 'a wrapped

  val has_type : 'a wrapped -> bool
  val has_sort : 'a wrapped -> bool
  val has_kind : 'a wrapped -> bool

  val get_type : 'a wrapped -> ty
  val get_sort : 'a wrapped -> ty_atom
  val get_kind : 'a wrapped -> ty_kind

  val query_type : 'a wrapped -> ty option
  val query_sort : 'a wrapped -> ty_atom option
  val query_kind : 'a wrapped -> ty_kind option
end

module Disambiguation : sig
  (* FIXME remove *)
  val any_special_prop : T_t.ty_atom Property.pfuncs
  (* FIXME remove *)
  val cast_special_prop : (T_t.ty_atom * T_t.ty_atom) Property.pfuncs
  (* FIXME remove *)
  val int_special_prop : unit Property.pfuncs
  (* FIXME remove *)
  val real_special_prop : unit Property.pfuncs
  (* FIXME remove *)
  val cast_nm : T_t.ty_atom -> T_t.ty_atom -> string
  val any_nm : T.ty_atom -> string
  val as_prop : T_t.ty_atom Property.pfuncs
  val min_reconstruct : Expr.T.sequent -> Expr.T.sequent
end

