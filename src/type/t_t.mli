(*
 * type/t.mli --- type system
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Property


(* {3 Types} *)

type ty =
  | TVar of string  (** Type variable *)
  | TAtm of atm     (** Atomic type *)
  | TSet of ty      (** Set-type *)
  | TFun of ty * ty (** Function-type *)
  | TPrd of ty list (** Product-type *)
and atm =
  | TAIdv           (** Individual *)
  | TABol           (** Boolean *)
  | TAInt           (** Integer *)
  | TARel           (** Real *)
  | TAStr           (** String *)

and ty0 = ty                    (** Constant type *)
and ty1 = Ty1 of ty0 list * ty  (** Fst-order operator type *)
and ty2 = Ty2 of ty1 list * ty  (** Snd-order operator type *)

module Ts : Set.S with type elt = ty
module Tm : Map.S with type key = ty

val upcast_ty1 : ty0 -> ty1
val upcast_ty2 : ty1 -> ty2

exception Invalid_type_downcast
val downcast_ty1 : ty2 -> ty1
val downcast_ty0 : ty1 -> ty0

val safe_downcast_ty1 : ty2 -> ty1 option
val safe_downcast_ty0 : ty1 -> ty0 option


(* {3 Type Substitution} *)

type ty_sub = ty Util.Coll.Sm.t

(** Apply subst to type *)
val apply_ty_sub  : ty_sub -> ty0 -> ty0
val apply_ty_sub1 : ty_sub -> ty1 -> ty1
val apply_ty_sub2 : ty_sub -> ty2 -> ty2


(* {Type Erasure} *)

(** Type erasure maps each type [t] to a type [t'] with the same structure, but
    all sorts different than Idv replaced with Idv.  Bool is special, it is
    preserved by type erasure.
*)
val erase0 : ty0 -> ty0
val erase1 : ty1 -> ty1
val erase2 : ty2 -> ty2


(* {3 Type Annotations} *)

module Props : sig
  val ty0_prop : ty0 pfuncs
  val ty1_prop : ty1 pfuncs
  val ty2_prop : ty2 pfuncs

  val tpars_prop : ty list pfuncs (** Type instances to polymorphics ops. *)
  val icast_prop : ty pfuncs      (** Forgetful injection into individuals *)
  val bproj_prop : ty pfuncs      (** Expressions occurring in boolean ctxt *)
end


(* {3 Pretty-printing} *)

(** String representation; no whitespaces *)
val ty_to_string : ty -> string

val pp_print_ty0 : Format.formatter -> ty0 -> unit
val pp_print_ty1 : Format.formatter -> ty1 -> unit
val pp_print_ty2 : Format.formatter -> ty2 -> unit
val pp_print_atm : Format.formatter -> atm -> unit

