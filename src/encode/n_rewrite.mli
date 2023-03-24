(*
 * encode/rewrite.mli --- rewrite sequents
 *
 *
 * Copyright (C) 2022  INRIA and Microsoft Corporation
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

(** Sort fields of records and record sets *)
val sort_recfields : sequent -> sequent

(** Simplify propositions involving ranges *)
val simplify_range : sequent -> sequent

(** Apply extensionality axioms to equalities; also simplifies subseteq *)
val apply_ext : sequent -> sequent

(** Simplify expressions of set theory
    @param limit specify the number of times expressions are parsed
    @param rwlvl if 0: do nothing;
                 1: only simplify set extensionality and subseteq;
                 2: simplify all set expressions;
                 3: like 2, but don't care about an expression's polarity
*)
val simplify_sets : ?limit:int -> ?rwlvl:int -> sequent -> sequent

