(*
 * encode/hints.mli --- add generic with-patterns on quantified forms
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** The idea is to detect a unary predicate with a certain name "With(X)".
    Any assertion "With(e)" should be read as an instanciation hint (for the
    term e).  It suffices to add the pattern "With(x)" for every universal
    binder '\A x' in a formula.
*)

open Expr.T

(** Name of the predicate that identifies the hint tactic *)
val with_id : string

(** Call after type reconstruction *)
val main : sequent -> sequent

