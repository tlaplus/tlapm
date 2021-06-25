(*
 * Copyright (C) 2011-2012  INRIA and Microsoft Corporation
 *)
open Expr.T

type t =
    | Int
    | Str
    | Bool
    | TyAtom of string
        (** Atomic type *)
    | Top
        (** Only for CHOOSE *)
    | TyVar of ty_subst list * string
        (** Variable type with
        delayed substitution *)
    | Set of t
        (** Power set type *)
    | Func of string * t * t
        (** Dependent function type *)
    | Ref of string * t * tref
        (** Refinement type *)
    | Rec of (string * t) list
    | Rec_dot of t * string
    | TyPlus of t list
    | TyTimes of t list
    | Tbase of t
        (** Base of refinement *)
    | Tdom of t
        (** Domain *)
    | Tcod of t
        (** Co-domain *)
and tref =
    | Ex of hyp list * expr
    | Ph of (ty_subst list * plhdr)
and plhdr = string
and ty_subst =
    string * hyp list * expr * t

(*
val to_scx:
    hyp list -> hyp Deque.dq
*)
val (<<<):
    'a Property.wrapped -> t ->
        'a Property.wrapped
val optype:
    'a Property.wrapped -> t option
val has_type:
    'a Property.wrapped -> bool

val is_atomic_type:
    t -> bool
val is_tyvar:
    t -> bool

val mk_ref:
    t -> t
(*
val is_safe:
    t -> bool
*)
(*
val is_int:
    t -> bool
*)
val eq:
    t -> t -> bool
val eq_ref:
    tref -> tref -> bool
(*
val eq_uptoref:
    t -> t -> bool
*)
val add_x_ctx:
    string -> t -> hyp list ->
        hyp list
val add_x_ref:
    string -> t -> tref -> tref
val fv:
    t -> string list
val tmap:
    (t -> t) -> t -> t
val subst:
    string -> t -> t -> t
(*
val subst_ss:
    string -> t -> ty_subst list ->
        ty_subst list
*)
val subst_ref:
    string -> t -> tref -> tref
val vsubst:
    string -> string -> t -> t
val unify_fails:
    t -> t -> bool
(*
val add_exp_one_subst:
    hyp list -> expr ->
    string -> t -> expr ->
        (hyp list * expr)
*)
val add_exp_substs:
    hyp list -> expr ->
    ty_subst list ->
        (hyp list * expr)
val simplify:
    t -> t
(*
val typbot:
    expr -> t
*)
val expr_fv:
    t -> string list
val occurs:
    string -> t -> bool
val base_to_ref:
    t -> t
val ref_to_base:
    t -> t

exception Typeinf_failed

(*
val ctr_types:
    int ref
*)
val ctr_funarg:
    int ref
val fresh_tyterm:
    unit -> string

val to_predtyp:
    hyp list -> expr -> t ->
        (t * hyp list * expr)

val lookup_type:
    hyp Deque.dq -> int -> t option
val lookup_type_by_id:
    hyp Deque.dq -> string -> t option
val get_type:
    hyp Deque.dq -> expr -> t option
val is_int:
    hyp Deque.dq -> expr -> bool
val is_bool:
    hyp Deque.dq -> expr -> bool
val is_hard_bool:
    expr -> bool
