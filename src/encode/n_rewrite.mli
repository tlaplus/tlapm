(*
 * encode/rewrite.mli --- rewrite sequents
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T

(** Bounds attached to variables (bound or declared) are eliminated
    and replaced by a guard.
*)
val elim_bounds : sequent -> sequent

(** Simplify NotMem *)
val elim_notmem : sequent -> sequent

(** Simplify Lt, Gteq and Gt *)
val elim_compare : sequent -> sequent

(** Reduce EXCEPT-functions to regular functions *)
val elim_except : sequent -> sequent

(** Reduce functions to one-argument functions (using tuples) *)
val elim_multiarg : sequent -> sequent
(** NOTE: Better not call after {!elim_tuples}, since this introduces new tuples *)

(** Reduce tuples to functions *)
val elim_tuples : sequent -> sequent

