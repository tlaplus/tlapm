(*
 * Copyright (C) 2012  INRIA and Microsoft Corporation
 *)

(** Packaging Module for TLA+'s Type System *)


(** Interface for the type and the constraint system *)
module T : sig
  open Property

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

  type ty_sub = ty Util.Coll.Sm.t

  val apply_ty_sub  : ty_sub -> ty0 -> ty0
  val apply_ty_sub1 : ty_sub -> ty1 -> ty1
  val apply_ty_sub2 : ty_sub -> ty2 -> ty2

  exception Typechecking_error of ty0 * ty0
  exception Typechecking_op_error of ty2 * ty2

  val typecheck : expected:ty0 -> actual:ty0 -> unit
  val typecheck_op : expected:ty2 -> actual:ty2 -> unit

  val typecheck_error_mssg : expected:ty0 -> actual:ty0 -> string
  val typecheck_op_error_mssg : expected:ty2 -> actual:ty2 -> string

  val erase0 : ty0 -> ty0
  val erase1 : ty1 -> ty1
  val erase2 : ty2 -> ty2

  module Props : sig
    val ty0_prop : ty0 pfuncs
    val ty1_prop : ty1 pfuncs
    val ty2_prop : ty2 pfuncs

    val tpars_prop : ty list pfuncs (** Type instances to polymorphics ops. *)
    val icast_prop : ty pfuncs      (** Forgetful injection into individuals *)
    val bproj_prop : ty pfuncs      (** Expressions occurring in boolean ctxt *)
  end

  val ty_to_string : ty -> string

  val pp_print_ty0 : Format.formatter -> ty0 -> unit
  val pp_print_ty1 : Format.formatter -> ty1 -> unit
  val pp_print_ty2 : Format.formatter -> ty2 -> unit
  val pp_print_atm : Format.formatter -> atm -> unit
end

module Collect : sig
  open Expr.T
  open T
  val main : sequent -> Ts.t
end

module Reconstruct : sig
  open Expr.T
  val main : sequent -> sequent
end

