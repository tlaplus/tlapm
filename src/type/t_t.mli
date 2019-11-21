(*
 * type/types.mli --- type system
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Util


type ty = 
  | TVar of string
  | TAtom of ty_atom
  | TArrow of ty * ty
  | TSet of ty

and ty_atom =
  | TInt | TStr | TBool


module Sm = Coll.Sm
type tmap = ty Sm.t


type cstr =
    | CAtom of cstr_atom
    | CConj of cstr list
    | CExists of string list * cstr

and cstr_atom =
    | CTrue
    | CFalse
    | CSynEq of ty * ty
    | CEq of ty * ty


(** Type annotations are implemented as properties of hints (strings). *)
val type_annot : hint -> ty -> hint
val has_type_annot : hint -> bool
val get_type_annot : hint -> ty
val get_opt_type_annot : hint -> ty option

(** Pretty-printer for types *)
val pp_print_type : Format.formatter -> ty -> unit
val pp_print_constraint : Format.formatter -> cstr -> unit

