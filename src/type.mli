(*
 * Copyright (C) 2012  INRIA and Microsoft Corporation
 *)

(** Packaging Module for TLA+'s Type System *)


(** Interface for the type and the constraint system *)
module T : sig
  open Util
  open Property

  type ty =
    | TVar of string
    | TAtom of ty_atom
    | TArrow of ty * ty
    | TProd of ty list
    | TSet of ty
    | TUnknown
  and ty_atom =
    | TBool | TAtSet | TInt | TReal | TStr

  module Sm = Coll.Sm
  type tmap = ty Sm.t

  val type_annot : hint -> ty -> hint
  val has_type_annot : hint -> bool
  val get_type_annot : hint -> ty
  val get_opt_type_annot : hint -> ty option

  val pp_print_type : Format.formatter -> ty -> unit

  module Props : sig
    val type_prop : ty pfuncs
  end
end

