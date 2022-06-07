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

(* FIXME The [op_typing] schema should be extended for dependent types
 * but this will have to wait.  For now, the function will redirect to one
 * of the special cases below. *)
val op_intquotient_typing : unit -> expr
val op_fsenum_typing : int -> ty0 -> expr (* This one is different, bc enum_n doesn't have an equivalent in CVC4's FS theory *)

val exttrigeq_def : ty0 -> expr
val exttrigeq_trigger : ty0 -> expr
val disjoint_trigger : unit -> expr
val emptycomprehension_trigger : unit -> expr
val exttrigeq_card : unit -> expr



(* {3 Main} *)

(* {4 Logic} *)

val choose_def : unit -> expr
val choose_ext : unit -> expr

(* {4 Sets} *)

val set_ext : ext:bool -> expr

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

val fcnexceptapp1_def : unit -> expr
val fcnexceptapp2_def : unit -> expr

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

val nonneg_ispos : unit -> expr

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

val seqlen_def : noarith:bool -> expr

val seqcat_typing : unit -> expr
val seqcatlen_def : noarith:bool -> expr
val seqcatapp1_def : noarith:bool -> expr
val seqcatapp2_def : noarith:bool -> expr

val seqappend_typing : unit -> expr
val seqappendlen_def : noarith:bool -> expr
val seqappendapp1_def : noarith:bool -> expr
val seqappendapp2_def : noarith:bool -> expr

val seqhead_def : noarith:bool -> expr

val seqtail_typing : noarith:bool -> expr
val seqtaillen_def : noarith:bool -> expr
val seqtailapp_def : noarith:bool -> expr

val seqsubseq_typing : noarith:bool -> expr
val seqsubseqlen_def : noarith:bool -> expr
val seqsubseqapp_def : noarith:bool -> expr

val seqselectseq_typing : unit -> expr
val seqselectseqlen_def : noarith:bool -> expr
val seqselectseqnil_def : unit -> expr
val seqselectseqappend_def : unit -> expr

val seqtup_typing : int -> expr
val seqtuplen_def : noarith:bool -> int -> expr

(* {4 Finite Sets} *)

val subseteq_isfs : unit -> expr
val enum_isfs : int -> expr
val subset_isfs : unit -> expr
val union_isfs : unit -> expr
val setst_isfs : unit -> expr
val setof_isfs : int -> expr
val cup_isfs : unit -> expr
val cap_isfs : unit -> expr
val setminus_isfs : unit -> expr
val product_isfs : int -> expr
val rect_isfs : string list -> expr
val range_isfs : unit -> expr

val card_typing : unit -> expr

val subseteq_card : noarith:bool -> expr
val empty_card : noarith:bool -> expr
val singleton_card : noarith:bool -> expr
val cup_card : noarith:bool -> expr
val cap_card : noarith:bool -> expr
val setminus_card : noarith:bool -> expr
val product_card : noarith:bool -> int -> expr
val rect_card : noarith:bool -> string list -> expr
val range_card : noarith:bool -> expr

val fsproduct_card : int -> expr (* FIXME not linked *)
val fsrect_card : string list -> expr (* FIXME not linked *)
val fsrange_card : unit -> expr (* FIXME not linked *)

