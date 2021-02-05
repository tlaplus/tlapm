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
  val elim_except : sequent -> sequent
  val elim_tuples : sequent -> sequent
  val elim_records : sequent -> sequent
  val apply_ext : sequent -> sequent
end

module CollectTypes : sig
  open Expr.T
  open Type.T
  val main : sequent -> Ts.t
end

module Table : sig
  open Property
  open Type.T
  type tla_smb =
    (* Logic *)
    | Choose of ty
    (* Set Theory *)
    | Mem of ty
    | SubsetEq of ty
    | SetEnum of int * ty
    | Union of ty
    | Subset of ty
    | Cup of ty
    | Cap of ty
    | SetMinus of ty
    | SetSt of ty
    | SetOf of ty list * ty
    (* Primitive Sets *)
    | Booleans
    | Strings
    | Ints
    | Nats
    | Reals
    (* Functions *)
    | IsAFcn
    | Arrow of ty * ty
    | Domain of ty * ty
    | FcnApp of ty * ty
    | Fcn of ty * ty
    | Except of ty * ty
    (* Arithmetic *)
    | Plus
    | Uminus
    | Minus
    | Times
    | Ratio
    | Quotient
    | Remainder
    | Exp
    | Lteq
    | Lt
    | Gteq
    | Gt
    | Range
    | IntLit of int
    (* Strings *)
    | StrLit of string
    (* Tuples *)
    | Product of ty list * int
    | Tuple of ty list * int
    (* Special *)
    | Any of ty
    | Ucast of ty
    | Uver of tla_smb
    | Error

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

  val get_tlafam : tla_smb -> family
  val smbtable : tla_smb -> (tla_smb list * Expr.T.expr list) option

  type smb

  module OrdSmb : sig
    type t = smb
    val compare : t -> t -> int
  end

  module SmbSet : Set.S with type elt = smb
  module SmbMap : Map.S with type key = smb

  val smb_prop : smb pfuncs
  val has_smb : 'a wrapped -> bool
  val set_smb : smb -> 'a wrapped -> 'a wrapped
  val get_smb : 'a wrapped -> smb

  val std_smb : tla_smb -> smb

  val mk_smb : family -> string -> ?sch:ty_sch -> ty_kind -> smb
  val mk_cst_smb : family -> string -> ty -> smb
  val mk_fst_smb : family -> string -> ty list -> ty -> smb
  val mk_snd_smb : family -> string -> (ty list * ty) list -> ty -> smb

  val get_fam  : smb -> family
  val get_name : smb -> string
  val get_sch  : smb -> ty_sch
  val get_kind : smb -> ty_kind
  val get_ord  : smb -> int
  val get_defn : smb -> tla_smb option
end

module Direct : sig
  open Expr.T
  val main : sequent -> sequent
end

module Canon : sig
  open Property
  open Expr.T
  open Type.T
  type gtx = ty_kind Ctx.t
  type ltx = ty_kind Ctx.t
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

module Axiomatize : sig
  open Property
  open Expr.T
  open Table
  type etx
  val mem : string -> etx -> bool
  val get_smb : string -> etx -> smb
  val get_axms : string -> etx -> expr list
  val map_etx : (smb -> expr -> expr) -> etx -> etx
  val axm_ptrs_prop : (int list) pfuncs
  val collect : sequent -> etx
  val assemble : etx -> sequent -> sequent
  val main : sequent -> sequent
end

module Reduce : sig
  open Expr.T

  val instantiate : sequent -> int -> expr -> sequent
  val main : sequent -> sequent
end

