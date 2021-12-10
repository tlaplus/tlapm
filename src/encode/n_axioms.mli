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

(** Return the actual expression for an axiom *)
val get_axm : solver:string -> tla_axm -> expr
(** You should only use this function.  The rest is for documentation. *)


(* {3 Special} *)

val cast_inj : ty0 -> expr
val cast_inj_alt : ty0 -> expr
val type_guard : ty0 -> expr
val type_guard_intro : ty0 -> expr
val type_guard_elim : ty0 -> expr
val op_typing : tla_smb -> expr


(* {3 Untyped/Monosorted Variants} *)

(* {4 Logic} *)

val choose_def : unit -> expr
val choose_ext : unit -> expr

(* {4 Sets} *)

val set_ext : unit -> expr

val subseteq_def : unit -> expr
val subseteq_intro : unit -> expr
val subseteq_elim : unit -> expr
val subseteq_antisym : unit -> expr

val setenum_def : int -> expr
val setenum_intro : int -> expr
val setenum_elim : int -> expr

val union_def : unit -> expr
val union_intro : unit -> expr
val union_elim : unit -> expr

val subset_def : unit -> expr
val subset_def_alt : unit -> expr
val subset_intro : unit -> expr
val subset_elim : unit -> expr

val cup_def : unit -> expr

val cap_def : unit -> expr

val setminus_def : unit -> expr

val setst_def : unit -> expr

val setof_def : int -> expr
val setof_intro : int -> expr
val setof_elim : int -> expr

(* {4 Functions} *)

val fcn_ext : unit -> expr

val fcnconstr_isafcn : unit -> expr

val fcndom_def : unit -> expr

val fcnapp_def : unit -> expr

val fcnset_def : unit -> expr
val fcnset_intro : unit -> expr
val fcnset_elim1 : unit -> expr
val fcnset_elim2 : unit -> expr
val fcnsetim_intro : unit -> expr
val fcnset_subs : unit -> expr

val fcnexcept_isafcn : unit -> expr

val fcnexceptdom_def : unit -> expr

val fcnexceptapp_def : unit -> expr

val fcnim_def : unit -> expr
val fcnim_intro : unit -> expr
val fcnim_elim : unit -> expr

(* {4 Strings} *)

val strlit_isstr : string -> expr

val strlit_distinct : string -> string -> expr

(* {4 Arithmetic} *)

val natset_def : noarith:bool -> expr
val intrange_def : unit -> expr

val intlit_distinct : int -> int -> expr
val intlit_zerocmp : int -> expr

val intlit_isint : int -> expr
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

val tupdom_def : noarith:bool -> t0p:bool -> int -> expr

val tupapp_def : noarith:bool -> int -> expr

val productset_def : int -> expr
val productset_intro : int -> expr
val productset_elim : noarith:bool -> int -> expr

(* {4 Records} *)

val record_isafcn : string list -> expr

val recdom_def : string list -> expr

val recapp_def : string list -> expr

val recset_def : string list -> expr
val recset_intro : string list -> expr
val recset_elim : string list -> expr

(* {4 Sequences} *)

val seqset_intro : noarith:bool -> expr
val seqset_elim1 : noarith:bool -> expr
val seqset_elim2 : noarith:bool -> expr

val seqlen_def : unit -> expr

val seqcat_isseq : unit -> expr
val seqcatlen_def : noarith:bool -> expr
val seqcatapp_def : noarith:bool -> expr

val seqappend_isseq : unit -> expr
val seqappendlen_def : noarith:bool -> expr
val seqappendapp_def : noarith:bool -> expr

val seqhead_def : noarith:bool -> expr

val seqtail_isseq : unit -> expr
val seqtaillen_def : noarith:bool -> expr
val seqtailapp_def : noarith:bool -> expr

val seqempty_isseq : unit -> expr
val seqemptylen_def : noarith:bool -> expr

val sequnit_isseq : unit -> expr
val sequnitlen_def : noarith:bool -> expr


(* {3 Typed Variants} *)

(* {4 Strings} *)

val t_strset_def : unit -> expr
val t_strlit_distinct : string -> string -> expr

(* {4 Arithmetic} *)

val t_intset_def : t0p:bool -> expr
val t_natset_def : t0p:bool -> expr
val t_intrange_def : t0p:bool -> expr

