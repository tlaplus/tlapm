(*
 * Copyright (C) 2022  INRIA and Microsoft Corporation
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
  val elim_flex : sequent -> sequent
  val elim_notmem : sequent -> sequent
  val elim_compare : sequent -> sequent
  val elim_except : sequent -> sequent
  val elim_multiarg : sequent -> sequent
  val elim_except : sequent -> sequent
  val elim_tuples : sequent -> sequent
  val elim_records : sequent -> sequent
  val sort_recfields : sequent -> sequent

  val simplify_range : sequent -> sequent
  val simplify_sets : ?limit:int -> ?rwlvl:int -> sequent -> sequent
end

module Table : sig
  open Type.T
  type tla_smb =
    | Choose
    | Mem
    | SubsetEq
    | SetEnum of int
    | Add
    | Union
    | Subset
    | Cup
    | Cap
    | SetMinus
    | SetSt
    | SetOf of int
    | BoolSet
    | StrSet
    | StrLit of string
    | IntSet
    | NatSet
    | IntLit of int
    | IntPlus
    | IntUminus
    | IntMinus
    | IntTimes
    | IntQuotient
    | IntRemainder
    | IntExp
    | IntLteq
    | IntLt
    | IntGteq
    | IntGt
    | IntRange
    | FunIsafcn
    | FunSet
    | FunConstr
    | FunDom
    | FunIm
    | FunApp
    | FunExcept
    | Tuple of int
    | Product of int
    | Rec of string list
    | RecSet of string list
    | SeqSeq
    | SeqLen
    | SeqBSeq
    | SeqCat
    | SeqAppend
    | SeqHead
    | SeqTail
    | SeqSubSeq
    | SeqSelectSeq
    | FSIsFiniteSet
    | FSCard
    | TIntLit of int
    | TIntPlus
    | TIntUminus
    | TIntMinus
    | TIntTimes
    | TIntQuotient
    | TIntRemainder
    | TIntExp
    | TIntLteq
    | TIntLt
    | TIntGteq
    | TIntGt
    | TFSCard of ty
    | TFSMem of ty
    | TFSSubseteq of ty
    | TFSEmpty of ty
    | TFSSingleton of ty
    | TFSAdd of ty
    | TFSCup of ty
    | TFSCap of ty
    | TFSSetminus of ty
    | Cast of ty
    | Proj of ty
    | True of ty
    | Anon of string * ty2
    | ExtTrigEq of ty
    | ExtTrig
    | IsSetOf
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
  val get_defn  : smb -> Table.tla_smb

  val pp_print_smb : Format.formatter -> smb -> unit
end

module Standardize : sig
  open Expr.T
  val main : sequent -> sequent
end

module Axiomatize : sig
  open Property
  open Expr.T
  val main : solver:string -> sequent -> sequent
end

module Flatten : sig
  open Expr.T
  val main : sequent -> sequent
end

