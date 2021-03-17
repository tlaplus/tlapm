(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

(* Packaging module for the modules that implement PO transformations *)

module Hints : sig
  open Expr.T
  val with_id : string
  val main : sequent -> sequent
end

module Rewrite : sig
  open Expr.T
  val elim_bounds : sequent -> sequent
  val elim_notmem : sequent -> sequent
  val elim_compare : sequent -> sequent
  val elim_except : sequent -> sequent
  val elim_multiarg : sequent -> sequent
  val elim_except : sequent -> sequent
  val elim_tuples : sequent -> sequent
  val elim_records : sequent -> sequent
  val simplify : sequent -> sequent
  val apply_ext : sequent -> sequent
end

module Smb : sig
  open Type.T
  open Property

  type smb
  val smb_prop : smb pfuncs
  module SmbSet : Set.S with type elt = smb
  val equal_smb : smb -> smb -> bool
  val get_name : smb -> string
  val get_ty2  : smb -> ty2
  val get_ty1  : smb -> ty1
  val get_ty0  : smb -> ty0
  val get_ord  : smb -> int

  val pp_print_smb : Format.formatter -> smb -> unit
end

module Standardize : sig
  open Expr.T
  val main : sequent -> sequent
end

module Axiomatize : sig
  open Property
  open Expr.T
  val main : sequent -> sequent
end

