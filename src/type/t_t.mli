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


(* {3 Type Annotations} *)

(** These properties are intended as annotations on hints *)
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


(* {3 Pretty-printing} *)

val pp_print_type : Format.formatter -> ty -> unit
val pp_print_atom : Format.formatter -> ty_atom -> unit
val pp_print_kind : Format.formatter -> ty_kind -> unit

