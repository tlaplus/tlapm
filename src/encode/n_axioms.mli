(*
 * encode/axioms.mli --- axioms for TLA+ symbols
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open Type.T

(** Mark some opaques as special. *)
val special_prop : unit Property.pfuncs
(* FIXME Better architecture for Table and Axioms *)

(* {3 Logic} *)

val choose : ty option -> expr

(* {3 Sets} *)

val subseteq : ty option -> expr
val setenum : int -> ty option -> expr
val union : ty option -> expr
val subset : ty option -> expr
val cup : ty option -> expr
val cap : ty option -> expr
val setminus : ty option -> expr
val setst : ty option -> expr
val setof : int -> (ty list * ty) option -> expr

(* {3 Functions} *)

val fcnisafcn : expr
val arrow : (ty * ty) option -> expr
val domain : (ty * ty) option -> expr
val fcnapp : (ty * ty) option -> expr

(* {3 Booleans} *)

val boolcast_inj : expr
val booleans : expr

(* {3 Strings} *)

val strings : expr

(* {3 Arithmetic} *)

val ints : expr
val nats : expr
val reals : expr

val int_guard : expr

