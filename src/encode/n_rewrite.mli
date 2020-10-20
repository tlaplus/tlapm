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

(** Eliminate NotMem *)
val elim_notmem : sequent -> sequent

(** Eliminate Lt, Gteq and Gt *)
val elim_compare : sequent -> sequent

(** Reduce functions to one-argument functions (using tuples) *)
val elim_multiarg : sequent -> sequent
(** NOTE: Better not call after {!elim_tuples}, since this introduces new tuples *)

(** Reduce tuples to functions *)
val elim_tuples : sequent -> sequent

(** Reduce records to functions *)
val elim_records : sequent -> sequent

