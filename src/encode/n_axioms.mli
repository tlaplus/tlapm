(*
 * encode/axioms.mli --- axioms for TLA+ symbols
 *
 *
 * Copyright (C) 2022  INRIA and Microsoft Corporation
 *)

open Expr.T
open Type.T

open N_table

(** Axioms used in the TPTP and SMT encodings, all in standard form
    (see {!Encode.Smb} and {!Encode.Standardize}).
    *)

(** Return the actual expression for an axiom
    @param disable_arithmetic      default=false; no link with solver's native arithmetic
    @param smt_set_extensionality  default=false; use special SMT triggers for set extensionality
    *)
val get_axm :
  solver:string ->
  ?disable_arithmetic:bool ->
  ?smt_set_extensionality:bool ->
  tla_axm -> expr
(** This is the only function from this module you should use.
    The rest below is documentation.
    *)


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
val op_intremainder_typing : unit -> expr

val exttrigeq_def : ty0 -> expr
val exttrigeq_trigger : ty0 -> expr
val disjoint_trigger : unit -> expr
val emptycomprehension_trigger : unit -> expr
val assert_issetof : int -> expr
val compare_setof_trigger : unit -> expr
val exttrigeq_card : unit -> expr



(* {3 Main} *)

(* {4 Logic} *)

val choose_def : unit -> expr
val choose_ext : unit -> expr

(* {4 Sets} *)

val set_ext : smt_set_extensionality:bool -> expr

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
val fcnconstr_typing : unit -> expr

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
val fcnexcept_typing : unit -> expr

val fcnim_def : unit -> expr
val fcnim_intro : unit -> expr
val fcnim_elim : unit -> expr

(* {4 Strings} *)

val strlit_isstr : string -> expr

val strlit_distinct : string -> string -> expr

(* {4 Arithmetic} *)

val natset_def : disable_arithmetic:bool -> expr
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
val intexp_typing : disable_arithmetic:bool -> expr
val natplus_typing : unit -> expr
val nattimes_typing : unit -> expr

val nonneg_ispos : unit -> expr

val lteq_reflexive : unit -> expr
val lteq_transitive : unit -> expr
val lteq_antisym : unit -> expr

(* {4 Tuples} *)

val tuple_isafcn : int -> expr
val tupdom_def : disable_arithmetic:bool -> int -> expr
val tupapp_def : disable_arithmetic:bool -> int -> expr
val tupexcept_def : disable_arithmetic:bool -> int -> int -> expr

val productset_def : int -> expr
val productset_intro : int -> expr
val productset_elim : disable_arithmetic:bool -> int -> expr

(* {4 Records} *)

val record_isafcn : string list -> expr
val recdom_def : string list -> expr
val recapp_def : string list -> expr
val recexcept_def : string list -> int -> expr

val recset_def : string list -> expr
val recset_intro : string list -> expr
val recset_elim : string list -> expr

(* {4 Sequences} *)

val seqset_intro : disable_arithmetic:bool -> expr
val seqset_elim1 : disable_arithmetic:bool -> expr
val seqset_elim2 : disable_arithmetic:bool -> expr

val seqlen_def : disable_arithmetic:bool -> expr

val seqcat_typing : unit -> expr
val seqcatlen_def : disable_arithmetic:bool -> expr
val seqcatapp1_def : disable_arithmetic:bool -> expr
val seqcatapp2_def : disable_arithmetic:bool -> expr

val seqappend_typing : unit -> expr
val seqappendlen_def : disable_arithmetic:bool -> expr
val seqappendapp1_def : disable_arithmetic:bool -> expr
val seqappendapp2_def : disable_arithmetic:bool -> expr

val seqhead_def : disable_arithmetic:bool -> expr

val seqtail_typing : disable_arithmetic:bool -> expr
val seqtaillen_def : disable_arithmetic:bool -> expr
val seqtailapp_def : disable_arithmetic:bool -> expr

val seqsubseq_typing : disable_arithmetic:bool -> expr
val seqsubseqlen_def : disable_arithmetic:bool -> expr
val seqsubseqapp_def : disable_arithmetic:bool -> expr

val seqselectseq_typing : unit -> expr
val seqselectseqlen_def : disable_arithmetic:bool -> expr
val seqselectseqnil_def : unit -> expr
val seqselectseqappend_def : unit -> expr

val seqtup_typing : int -> expr
val seqtuplen_def : disable_arithmetic:bool -> int -> expr

