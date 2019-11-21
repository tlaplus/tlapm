(*
 * type/types.ml --- type system
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Util


(** Types *)
type ty = 
  | TVar of string
  | TAtom of ty_atom
  | TArrow of ty * ty
  | TSet of ty

(** Atomic types *)
and ty_atom =
  | TInt | TStr | TBool


module Sm = Coll.Sm
type tmap = ty Sm.t


(** Constraints *)
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

let tprop : ty Property.pfuncs =
    Property.make "Smtlib.Types.ty"

let type_annot h ty =
    Property.assign h tprop ty

let has_type_annot h =
    Property.has h tprop

let get_type_annot h =
    Property.get h tprop

let get_opt_type_annot h =
    Property.query h tprop


(** Pretty-printing *)

let rec pp_print_type ppf ty =
    not_implemented "Smtlib.Types.pp_print_type"

let rec pp_print_constraint ppf cstr =
    not_implemented "Smtlib.Types.pp_print_type"

