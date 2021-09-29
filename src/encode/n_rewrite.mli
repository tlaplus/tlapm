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

(** Every [Flex v] replaced by two declarations for [v] and [v'],
    with occurrences of [Opaque v'] replaced by an index.
*)
val elim_flex : sequent -> sequent

(** Simplify NotMem *)
val elim_notmem : sequent -> sequent

(** Simplify Lt, Gteq and Gt *)
val elim_compare : sequent -> sequent

(** Reduce EXCEPT-functions to regular functions *)
val elim_except : sequent -> sequent

(** Reduce functions to one-argument functions (using tuples) *)
val elim_multiarg : sequent -> sequent
(** NOTE: Call before {!elim_tuples}, since this introduces new tuples *)

(** Reduce tuples to functions *) (* FIXME remove *)
val elim_tuples : sequent -> sequent

(** Reduce records to functions *) (* FIXME remove *)
val elim_records : sequent -> sequent

(** Apply extensionnality axioms to equalities *)
val apply_ext : sequent -> sequent

(** Simplify positive subset relations *)
val simpl_subseteq : sequent -> sequent

(** Simplify expressions of set theory *)
val simplify_sets : sequent -> sequent
(** NOTE Rewriting rules are applied bottom-up, and there may be
    residual redexes.  The function itself terminates, but calling it
    while there are possible reductions may not (Russell's paradox is
    an example).
*)

