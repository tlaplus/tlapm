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
  and ty_op =
    | TOp of ty_op list * ty

  module Sm = Coll.Sm
  type tmap = ty Sm.t

  val ty_u    : ty
  val ty_bool : ty
  val ty_int  : ty
  val ty_real : ty
  val ty_str  : ty

  val mk_atom_ty  : ty_atom -> ty
  val mk_op_ty    : ty_op list -> ty -> ty_op
  val mk_cst_ty   : ty -> ty_op
  val mk_fstop_ty : ty list -> ty -> ty_op

  val get_atom  : ty -> ty_atom
  val get_ty    : ty_op -> ty

  val get_atoms : ty -> ty_atom list

  val pp_print_type : Format.formatter -> ty -> unit

  module Props : sig
    val type_prop : ty pfuncs
    val sort_prop : ty_atom pfuncs
    val tyop_prop : ty_op pfuncs
  end
end

module MinRecon : sig
  val u_cast : T.ty_atom -> string
  val min_reconstruct : Expr.T.sequent -> Expr.T.sequent
end

