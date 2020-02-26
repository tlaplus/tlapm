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

(** Get free vars and bounded vars (respectively).
 
    A variable is bounded if its index is < to its depth, accounting for
    the context ctx; otherwise it is free.

    Most of the time we will want to know which variables are free from the
    current local context, which can be done by providing an empty ctx.  For
    this reason this is the default value for ctx.
*)
val  vs : ?ctx:ctx -> expr -> Is.t * Is.t
val bvs : ?ctx:ctx -> expr -> Is.t
val fvs : ?ctx:ctx -> expr -> Is.t


(* {3 Opaques} *)

(** Get all opaque strings in expression.  Context is irrelevant.
    
    The properties attached to a string s are those of the (Opaque s).
*)
val opaques : ?ctx:ctx -> expr -> Hs.t
