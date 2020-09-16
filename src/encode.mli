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

