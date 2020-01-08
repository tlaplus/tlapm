(*
 * type/t.mli --- type system
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Util
open Property


(* {3 Generalities} *)

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

module Props : sig
  val type_prop : ty pfuncs
end

val ty_bool : ty
val ty_aset : ty
val ty_int : ty
val ty_real : ty
val ty_str : ty

val get_atom : ty -> ty_atom
val get_atoms : ty -> ty_atom list


(* {3 Type Annotations} *)

val type_annot : hint -> ty -> hint
val has_type_annot : hint -> bool
val get_type_annot : hint -> ty
val get_opt_type_annot : hint -> ty option


(* {3 Pretty-printing} *)

val pp_print_type : Format.formatter -> ty -> unit

