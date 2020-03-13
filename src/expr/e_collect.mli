(*
 * expr/collect.mli --- collect data from expressions
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open E_t
open Util.Coll

type ctx = hyp Deque.dq


(* {3 Variables} *)

(** We want to manipulate the indexes rather than strings or hints. *)
type var_set = Is.t

val get_hints   : ctx -> var_set -> Hs.t
val get_strings : ctx -> var_set -> Ss.t

(** Helpers *)
val vs_fold : ctx -> (int -> hyp -> 'a -> 'a) -> var_set -> 'a -> 'a
val vs_partition : ctx -> (int -> hyp -> bool) -> var_set -> var_set * var_set

(** [fvs ~ctx e] returns the set of free variables in [e] assuming the local
    context [ctx].  That means the expression is virtually treated as if it was
    '\A (vars in ctx) : e'.

    The returned variables are represented as their De Bruijn indexes.  Default
    [ctx] is the empty context.

    NOTE: The indexes are calibrated relative to [ctx].  So the index [1] is
    not the variable at the rear of [ctx], but rather the lowest index that is
    *not* bound in [ctx].
*)
val fvs : ?ctx:ctx -> expr -> Is.t


(* {3 Opaques} *)

(** Get all opaque strings in expression.  Context is irrelevant.
    
    The properties attached to a string s are those of the (Opaque s).
*)
val opaques : ?ctx:ctx -> expr -> Hs.t
