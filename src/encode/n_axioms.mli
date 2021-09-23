(*
 * encode/axioms.mli --- axioms for TLA+ symbols
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open Type.T

open N_table

(** Axioms used in the encoding, all in standard form (see
    {!Encode.Smb} and {!Encode.Standardize}).

    All axioms are generated lazily because some parameters
    may affect their statements.
*)

(** You may use only this function.  Everything below is for documentation. *)
val get_axm : solver:string -> tla_axm -> expr


(* {3 Special} *)

val cast_inj : ty0 -> expr
val type_guard : ty0 -> expr
val op_typing : tla_smb -> expr


(* {3 Untyped/Monosorted Variants} *)

(* {4 Logic} *)

val choose_def : unit -> expr
val choose_ext : unit -> expr

(* {4 Sets} *)

val set_ext : unit -> expr
val subseteq_def : unit -> expr
val setenum_def : int -> expr
val union_def : unit -> expr
val subset_def : unit -> expr
val cup_def : unit -> expr
val cap_def : unit -> expr
val setminus_def : unit -> expr
val setst_def : unit -> expr
val setof_def : int -> expr

val subseteq_def_alt1 : unit -> expr
val subseteq_def_alt2 : unit -> expr
val setenum_def_alt1 : int -> expr
val setenum_def_alt2 : int -> expr

(* {4 Functions} *)

val fcn_ext : unit -> expr
val fcnconstr_isafcn : unit -> expr
val fcnset_def : unit -> expr
val fcndom_def : unit -> expr
val fcnapp_def : unit -> expr
val fcnexcept_isafcn : unit -> expr
val fcnexceptdom_def : unit -> expr
val fcnexceptapp_def : unit -> expr

(* {4 Strings} *)

val strlit_isstr : string -> expr
val strlit_distinct : string -> string -> expr

(* {4 Arithmetic} *)

val natset_def : noarith:bool -> expr
val intrange_def : unit -> expr
val intlit_isint : int -> expr
val intlit_distinct : int -> int -> expr
val intlit_zerocmp : int -> expr
val intplus_typing : unit -> expr
val intuminus_typing : unit -> expr
val intminus_typing : unit -> expr
val inttimes_typing : unit -> expr
val intquotient_typing : unit -> expr
val intremainder_typing : unit -> expr
val intexp_typing : unit -> expr
val natplus_typing : unit -> expr
val nattimes_typing : unit -> expr
val lteq_reflexive : unit -> expr
val lteq_transitive : unit -> expr
val lteq_antisym : unit -> expr

(* {4 Tuples} *)

val tuple_isafcn : int -> expr
val productset_def : noarith:bool -> int -> expr (* not used *)
val tupdom_def : noarith:bool -> t0p:bool -> int -> expr
val tupapp_def : noarith:bool -> int -> int -> expr

val productset_def_alt1 : int -> expr
val productset_def_alt21: int -> expr
val productset_def_alt22: int -> expr

(* {4 Records} *)

val record_isafcn : string list -> expr
val recset_def : string list -> expr
val recset_def_alt : string list -> expr
val recdom_def : string list -> expr
val recapp_def : string list -> expr

(* {4 Sequences} *)

val tail_isseq : unit -> expr


(* {3 Typed Variants} *)

(* {4 Strings} *)

val t_strset_def : unit -> expr
val t_strlit_distinct : string -> string -> expr

(* {4 Arithmetic} *)

val t_intset_def : t0p:bool -> expr
val t_natset_def : t0p:bool -> expr
val t_intrange_def : t0p:bool -> expr

