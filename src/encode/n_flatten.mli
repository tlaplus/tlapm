(*
 * encode/flatten.mli --- eliminate second-order features
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T

(** TLA+ expressions may contain second-order applications:

        F(e1, e2, .., G1, G2, ..)     where Gi are operators or LAMBDAs

    The purpose of flattening is to replace these applications by first-order
    ones:

        F_g(e1, e2, .., z1, z2, ..)   where zj are the free variables of all Gi

    The function {!main} is defined on sequents.  Applications are rewritten
    in all hypotheses and the goal.  Declarations are inserted for the new
    operators, and in some special cases, axioms are also added.

    Axioms for a given operator are recognized with {!N_smb.smb_prop}
    annotations.  If the same annotation is placed on the declaration of an
    operator, and a subsequent fact, then each flattening involving that
    operator will trigger an instantiation of the fact.

    This module is implemented for standardized expressions.  See the module
    {!N_standardize}.
*)

(* Signatures are included for documentation *)


(* {3 Context} *)

(** Context partitioned into a global and a local sections.

      ctx = (k, cx) where:
        cx is a double-ended queue that represents the context proper and
        k is an int that indicates the size of the global section

    The size of the local context is given by: size(cx) - k.
*)
type ctx = int Expr.Visit.scx


(* {3 Blueprints} *)

(** A blueprint is a record of all information relevant
    to an application waiting to be flattened.
*)
type bp


(* {3 Main} *)

(** [find_hoapp ctx e] returns some [bp] and [e'] if [e] contains a HO
    application.  [bp] is the blueprint for that application, [e'] is [e]
    with the application marked for later.
    Returns [None] if [e] does not contain a HO application.
*)
val find_hoapp : ctx -> expr -> (bp * expr) option

(** [mk_flat_declaration bp] is the declaration of a first-order operator
    for flattening the HO application that triggered [bp].
*)
val mk_flat_declaration : bp -> hyp

(** [find_axms bp] returns a list of closed expressions that must
    be instantiated in order to specify the flattened operator.
    Renamings are applied to each axiom so all are calibrated to the
    global context of [bp].
*)
val find_axms : bp -> expr list

(** [instantiate bp e] returns [e'] obtained by instantiating [e] with
    the HO arguments recorded in [bp].  Additionnally, every occurrence of the
    applied HO operator in that axiom is marked, so that it can be identified
    later for rewriting.
*)
val instantiate : bp -> expr -> expr

(** [rewrite_expr bp s e] rewrites the applications of [e] that are marked with
    the identifier of [bp] into flattened applications.  [s] is the index of
    the new operator.
*)
val rewrite_expr : bp -> int -> expr -> expr

(** Main function; you should only use this one. *)
val main : sequent -> sequent

