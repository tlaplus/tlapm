(*
 * encode/axioms.mli --- axioms for TLA+ symbols
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open Type.T

(** Axioms used in the encoding, all in standard form (see
    {!Encode.Standardize}).

    Axioms are generated lazily because some parameters may affect their
    statements (eg. {!Params.enc_typepreds}).
*)

val get_axm : N_table.tla_axm -> expr

(* {3 Special} *)

val cast_inj : ty0 -> expr
val type_guard : ty0 -> expr
val op_typing : N_table.tla_smb -> expr


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

(* {4 Functions} *)

val fcn_ext : unit -> expr
val fcnconstr_isafcn : unit -> expr
val fcnset_def : unit -> expr
val fcndom_def : unit -> expr
val fcnapp_def : unit -> expr

(* {4 Strings} *)

val strlit_isstr : string -> expr
val strlit_distinct : string -> string -> expr

(* {4 Arithmetic} *)

val intlit_isint : int -> expr
val intlit_distinct : int -> int -> expr
val natset_def : unit -> expr
val intplus_typing : unit -> expr
val intuminus_typing : unit -> expr
val intminus_typing : unit -> expr
val inttimes_typing : unit -> expr
val intquotient_typing : unit -> expr
val intremainder_typing : unit -> expr
val intexp_typing : unit -> expr
val intrange_def : unit -> expr

(* {4 Tuples} *)

val tuple_isafcn : int -> expr
val productset_def : int -> expr
val productset_def_alt : int -> expr
val tupdom_def : int -> expr
val tupapp_def : int -> int -> expr

(* {4 Records} *)

val record_isafcn : string list -> expr
val recset_def : string list -> expr
val recset_def_alt : string list -> expr
val recdom_def : string list -> expr
val recapp_def : string list -> expr


(* {3 Typed Variants} *)

(* {4 Strings} *)

val t_strlit_distinct : string -> string -> expr

(* FIXME adapt *)
(*

(* {3 Schema Instances} *)

(* FIXME See in reduce how the param is set *)
val inst_choose : (ty * ty list) option -> int -> expr -> expr
val inst_setst : (ty * ty list) option -> int -> expr -> expr
val inst_setof : int -> (ty list * ty * ty list) option -> int -> expr -> expr

*)
