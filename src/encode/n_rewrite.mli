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
(** NOTE: Call before {!elim_tuples}, since this introduces new tuples *)

(** Reduce tuples to functions *) (* FIXME remove *)
val elim_tuples : sequent -> sequent

(** Reduce records to functions *) (* FIXME remove *)
val elim_records : sequent -> sequent

(** Simplify by applying standard axioms *)
(* TODO *)
val simplify : sequent -> sequent
(** This includes:
    - `x \in {}` --> `FALSE`
    - `x \in {a, b}` --> `x = a \/ x = b`
    - `x \in { y \in S : P(y) }` --> `x \in S /\ P(x)`
    - `[ x \in S |-> F(x) ][z]` --> `IF z \in S THEN F(z) ELSE @`
      where `@` is the original expression
    - etc.
*)

(** Apply extensionnality axioms to equalities *)
val apply_ext : sequent -> sequent

