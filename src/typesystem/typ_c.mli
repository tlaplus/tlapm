(*
 * Copyright (C) 2011-2012  INRIA and Microsoft Corporation
 *)
open Expr.T

(****************************************************************************)
open Typ_t
open Typ_e

(* type substitutions = (string * Typ_t.t) list *)
(* val subs: substitutions ref *)
(*
val pp_subs:
    Format.formatter -> substitutions ->
        unit
*)

(* type judg_imp = Typ_e.t * hyp list * expr * hyp list * expr
val vcs: judg_imp list ref
val pp_vcs:
    Format.formatter -> judg_imp list ->
        unit
*)

type tc =  (** Atomic constraints *)
    | CTrue
    | CFalse
    | CEq of Typ_e.t * Typ_t.t * Typ_t.t
        (** Equality unification *)
    | CIsEq of Typ_e.t * Typ_t.t * Typ_t.t
        (** Syntactic equality on ground types *)
    | CSub of Typ_e.t * Typ_t.t * Typ_t.t
        (** Subtyping unification *)
    | CIsSub of Typ_e.t * Typ_t.t * Typ_t.t
        (** Syntactic subtype on ground types *)
and t =  (** Structural constraints *)
    | CAtom of tc
    | CConj of t list
    | CExists of string list * t

val pp:
    Format.formatter -> Typ_e.t * t ->
        unit
val ppc:
    Format.formatter -> Typ_e.t * tc ->
        unit
(* val closure : t -> t *)
val eq:
    t -> t -> bool
val eqc:
    tc -> tc -> bool
val simplify:
    Typ_e.t * t -> (Typ_e.t * t)
(* val solve_residual_iseq : Typ_e.t -> t -> Typ_e.t * t *)
val subst:
    string -> Typ_t.t -> t -> t
val substc:
    string -> Typ_t.t -> tc -> tc
val vsubst:
    string -> string -> t -> t
val subs_ss:
    string -> Typ_t.t ->
    (string * Typ_t.t) list ->
        (string * Typ_t.t) list
val app_ss:
    (string -> Typ_t.t -> 'a -> 'a) ->
    'a list -> (string * Typ_t.t) list ->
        'a list
val apply_ss:
    (string * Typ_t.t) list ->
    (Typ_e.t * string list * t list) ->
        (Typ_e.t * string list * t list)
val fv:
    t -> string list
val fix:
    ('a -> 'a -> bool) ->
    ('a -> 'a) -> 'a ->
        'a
val fix_env_c:
    (Typ_e.t * t -> Typ_e.t * t) ->
    (Typ_e.t * t) ->
        (Typ_e.t * t)
(*
val pp_env_c:
    Typ_e.t -> t -> unit
*)
(*
val c_to_cset:
    (Typ_e.t * t) ->
        (Typ_e.t * string list * tc list)
*)
(*
val flatten_cconj:
    t -> t list
*)
(*
val simp0:
    t -> t
*)
val map_c:
    (t -> t) -> t -> t
val simp_c:
    t -> t

type tcc_raw = Builtin.builtin * Typ_e.t * tref * tref
    (** Unprocessed TCC *)
val tccs:
    tcc_raw list ref
val pp_tccs:
    Format.formatter -> tcc_raw list -> unit
val tcc_subst:
    string -> Typ_t.t -> tcc_raw -> tcc_raw

(* val simp_ccs : tc list -> tc list *)
val rewrite_eqs:
    Typ_e.t * string list * t list ->
        Typ_e.t * string list * t list
val rw_c:
    (Typ_e.t * string list * t list ->
        Typ_e.t * string list * t list) ->
    Typ_e.t * t ->
        Typ_e.t * t
val mk_cs:
    t list -> t
val mk_ex:
    string list * t list -> t
val base_to_ref:
    t -> t
val iseq_to_eq:
    t -> t
val issub_to_sub:
    t -> t
(* val sub_to_eq_vars : t -> t *)
val c_length:
    t -> int

type cg_mode =
    | OnlySafe (* Only safe types, no unification *)
    | TypHyp   (* As a typing hypothesis *)

val ctr_phs:
    int ref
val phs:
    (hyp list * expr) SMap.t ref
val phs_log:
    (((string * Typ_t.t) *
        Typ_e.t * hyp list * expr)
            option) SMap.t ref
val new_ph:
    ((string * Typ_t.t) *
            Typ_e.t * hyp list * expr)  option ->
        string
val pp_ph: string ->
    (hyp list * expr) -> unit
