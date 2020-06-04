(*
 * encode/table.mli --- table of symbols used to encode POs
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Type.T


(* {3 Symbols of TLA+} *)

(** Abstract type of TLA+ symbols. *)
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
  | Arrow of ty * ty
  | Domain of ty * ty
  | FcnApp of ty * ty
  | Fcn of ty * ty
  | Except of ty * ty
  (* Special *)
  | Uver of tla_smb (** Uninterpreted VERsion of a symbol *)

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

(** Dependencies between symbols and axioms attached to symbols. *)
val smbtable : tla_smb -> (tla_smb list * Expr.T.expr list) option
(** Not implemented as a table because there is an infinite number of symbols *)


(* {3 Symbol Data} *)

(** Abstract type of a symbol: name + kind *)
type smb

module OrdSmb : sig
  type t = smb
  val compare : t -> t -> int
end

module SmbSet : Set.S with type elt = smb
module SmbMap : Map.S with type key = smb

(** Get concrete smb of a TLA+ symbol *)
val std_smb : tla_smb -> smb

val mk_smb : family -> string -> ty_kind -> smb
val mk_cst_smb : family -> string -> ty -> smb
val mk_fst_smb : family -> string -> ty list -> ty -> smb
val mk_snd_smb : family -> string -> (ty list * ty) list -> ty -> smb

val get_fam  : smb -> family
val get_name : smb -> string
val get_kind : smb -> ty_kind
val get_ord  : smb -> int
val get_defn : smb -> tla_smb option

