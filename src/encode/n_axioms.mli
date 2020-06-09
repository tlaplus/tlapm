(*
 * encode/axioms.mli --- axioms for TLA+ symbols
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open Type.T

(* {3 Logic} *)

val choose : ty -> expr

(* {3 Sets} *)

val subseteq : ty -> expr
val setenum : int -> ty -> expr
val union : ty -> expr
val subset : ty -> expr
val cup : ty -> expr
val cap : ty -> expr
val setminus : ty -> expr
val setst : ty -> expr
val setof : ty list -> ty -> expr

(* {3 Functions} *)

val arrow : ty -> ty -> expr
val domain : ty -> ty -> expr
val fcnapp : ty -> ty -> expr
val except : ty -> ty -> expr

(* {3 Booleans} *)

val booleans : expr

(* {3 Strings} *)

val strings : expr

(* {3 Arithmetic} *)

val ints : expr
val nats : expr
val reals : expr

