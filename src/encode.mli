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
  val elim_multiarg : sequent -> sequent
  val elim_tuples : sequent -> sequent
end

module CollectTypes : sig
  open Expr.T
  open Type.T
  val main : sequent -> Ts.t
end

module Smb : sig
  open Type.T
  open Property

  type 'a smb
  val mk_smb : string -> ty2 -> 'a -> 'a smb
  val get_name : 'a smb -> string
  val get_ty2  : 'a smb -> ty2
  val get_ty1  : 'a smb -> ty1
  val get_ty0  : 'a smb -> ty0
  val get_ord  : 'a smb -> int
  val get_defn : 'a smb -> 'a

  val fold : ('b -> 'a -> 'b) -> 'b -> 'a smb -> 'b
  val map  : ('a -> 'b) -> 'a smb -> 'b smb
  val iter : ('a -> unit) -> 'a smb -> unit

  val pp_print_smb : ?pp_print_defn:(Format.formatter -> 'a -> unit) -> Format.formatter -> 'a smb -> unit
end

