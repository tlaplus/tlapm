(*
 * Copyright (C) 2012  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev$"

(** Packaging Module for TLA+'s Type System *)


(** Interface for the type and the constraint system *)
module T : sig
  open Util

  type ty = 
    | TVar of string
    | TAtom of t_atom
    | TArrow of ty * ty
    | TSet of ty
  and t_atom =
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
end

(** Constraint generation *)
module CGen : sig
  open Expr.T

  val cgenerate : sequent -> sequent * T_t.cstr
end

(** Constraint solving *)
module CSolve : sig
  val csolve : T.cstr -> T.tmap
end

(** Main procedure *)
module Infer : sig
  open Expr.T

  val infer : sequent -> sequent
end

