(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

(* Packaging module for the modules that implement PO transformations *)

module Table : sig
  open Type.T
  type family =

    | Logic
    | Sets
    | Booleans
    | Strings
    | Tuples
    | Functions
    | Records
    | Sequences
    | Arithmetic
    | Special

  type smb

  val mk_smb : family -> string -> ty_kind -> smb
  val mk_cst_smb : family -> string -> ty -> smb
  val mk_fst_smb : family -> string -> ty list -> ty -> smb
  val mk_snd_smb : family -> string -> (ty list * ty) list -> ty -> smb
  val get_fam  : smb -> family
  val get_name : smb -> string
  val get_kind : smb -> ty_kind
  val get_ord  : smb -> int

  module OrdSmb : sig
    type t = smb
    val compare : t -> t -> int
  end

  module SmbSet : Set.S with type elt = smb

  val u_kind : ty_kind -> ty_kind
  val u_smb : smb -> smb

  val choose : ty -> smb

  val mem : ty -> smb
  val subseteq : ty -> smb
  val setenum : int -> ty -> smb
  val union : ty -> smb
  val subset : ty -> smb
  val cup : ty -> smb
  val cap : ty -> smb
  val setminus : ty -> smb
  val setst : ty -> smb
  val setof : ty list -> ty -> smb

  val set_boolean : smb
  val set_string : smb
  val set_int : smb
  val set_nat : smb
  val set_real : smb

  val arrow : ty -> ty -> smb
  val domain : ty -> ty -> smb
  val fcnapp : ty -> ty -> smb
  val fcn : ty -> ty -> smb
  val except : ty -> ty -> smb

  val product : ty list -> smb
  val tuple : ty list -> smb
end

module Canon : sig
  open Property
  open Expr.T
  open Type.T
  type gtx = ty_kind Ctx.t
  type ltx = ty_kind Ctx.t
  val smb_prop : Table.smb pfuncs
  val has_smb : 'a wrapped -> bool
  val set_smb : Table.smb -> 'a wrapped -> 'a wrapped
  val get_smb : 'a wrapped -> Table.smb
  val expr : gtx -> ltx -> expr -> expr * ty
  val sequent : gtx -> sequent -> gtx * sequent
  val defn : gtx -> ltx -> defn -> defn
  val defns : gtx -> ltx -> defn list -> ltx * defn list
  val bound : gtx -> ltx -> bound -> bound
  val bounds : gtx -> ltx -> bound list -> ltx * bound list
  val hyp : gtx -> hyp -> hyp
  val hyps : gtx -> hyp Deque.dq -> gtx * hyp Deque.dq

  val main : sequent -> sequent
end

module Reduce : sig
  open Expr.T

  val main : sequent -> sequent
end

module Axiomatize : sig
  open Expr.T

  val main : sequent -> sequent
end

