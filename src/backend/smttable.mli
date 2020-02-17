(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

open Expr.T
open Type.T

(** Symbol management for SMT-LIB encodings.

    When encoding a TLA+ expression, there may be symbols that need to be
    declared and axiomatised in the resulting SMT problem. These symbols may
    depend on others, so that one declaration leads to several.

    This module provides generic functions to print declarations, collect
    relevant symbols from TLA+ expressions, and compute the transitive closure
    of a dependency graph. Different encodings may rely on different systems of
    symbols; one system is implemented by an instance of the module type
    {!Collector} (symbol types and collector) along with an instance of
    {!Deps} (dependency graph).

    To this day there is one system of symbols that is implemented:
      - {!NT_Collector} the simplest system, used for the 'No Types' encoding
*)


(* {3 Generic SMT Declarations} *)

type fmt = Format.formatter -> unit -> unit

type smb =
  | Srt of int
  | Fun of ty_atom list * ty_atom
  | Axm of fmt

type decl =
  { id : string
  ; content : smb
  ; hidden : bool
  }

val mk_sdecl : ?hidden:bool -> string -> int -> decl
val mk_fdecl : ?hidden:bool -> string -> ty_atom list -> ty_atom -> decl
val mk_adecl : ?hidden:bool -> string -> fmt -> decl

val pp_print_decl : Format.formatter -> decl -> unit


(* {3 Abstract Symbols} *)

module type Collector = sig
  type smb
  val get_id : smb -> string
  val get_decl : smb -> decl
  val collect : sequent -> smb Sm.t
end

module type Deps = sig
  module C : Collector
  val deps : C.smb -> C.smb Sm.t
end

module Make (D : Deps) : Collector with type smb = D.C.smb


(* {3 Concrete Tables} *)

(* {4 No Types Encoding} *)

(** The 'No Types' (NT) encoding only uses the following basic sorts:
      - [set] for most non-boolean expression;
      - [bool] for boolean expressions (formulas);
      - other sorts such as [int] for specialized expressions, like
        literals.
*)
type nt_srt_t =
  | NT_Set
  | NT_Bool
  | NT_Int
  | NT_Real
  | NT_Str

(** The NT encoding is a straightforward translation of TLA+ into MS-FOL;
    most TLA+ operators are encoded using uninterpreted functions (in the TLA
    or Arith family), which are then axiomatised. The expression may contain
    casts (Cast family) which were inserted during the first phase of the
    encoding (see {!Type.MinRecon}).
*)
type nt_fun_t =
  | NT_TLA_STRING
  | NT_TLA_BOOLEAN
  | NT_TLA_SUBSET
  | NT_TLA_UNION
  | NT_TLA_DOMAIN
  | NT_TLA_subseteq
  | NT_TLA_in
  | NT_TLA_setminus
  | NT_TLA_cap
  | NT_TLA_cup
  | NT_TLA_Enum of int
  | NT_TLA_Prod of int
  | NT_TLA_tuple of int
  | NT_TLA_fcnapp
  | NT_TLA_Arrow
  | NT_TLA_Rect of int
  | NT_TLA_record of int
  | NT_TLA_except
  | NT_Arith_N
  | NT_Arith_Z
  | NT_Arith_R
  | NT_Arith_plus
  | NT_Arith_uminus
  | NT_Arith_minus
  | NT_Arith_ratio
  | NT_Arith_quotient
  | NT_Arith_remainder
  | NT_Arith_exp
  | NT_Arith_intexp
  | NT_Arith_Infinity
  | NT_Arith_range
  | NT_Arith_intrange
  | NT_Arith_lteq
  | NT_Arith_lt
  | NT_Arith_gteq
  | NT_Arith_gt
  | NT_Cast_BoolToSet
  | NT_Cast_IntToSet
  | NT_Cast_IntToReal
  | NT_Cast_RealToSet
  | NT_Cast_StrToSet

(* TODO add the missing axioms *)
type nt_axm_t =
  | NT_SetExt
  | NT_SubseteqDef
  | NT_EmptyDef
  | NT_EnumDef of int

type nt_smb =
  | NT_Srt of nt_srt_t
  | NT_Fun of nt_fun_t
  | NT_Axm of nt_axm_t

module NT_Collector : Collector with type smb = nt_smb

