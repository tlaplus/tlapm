(*
 * Copyright (C) 2011-2012  INRIA and Microsoft Corporation
 *)
open Expr.T
open Typ_t

module SMap : Map.S with type key = string
val tyvar_assignment : ((hyp list * expr) option * bool * Typ_t.t option) SMap.t ref
val tyvar_assignment_subst : string -> Typ_t.t -> unit
val tyvar_assignment_pp : int -> unit
val tyvar_assignment_simp : unit -> unit

module SSet : Set.S with type elt = string
val type_equiv : SSet.t SMap.t ref
val type_equiv_find : string -> (string * SSet.t) option
val type_equiv_union : string -> string -> unit
val add_type_equiv : string -> string -> unit
val type_equiv_pp : int -> unit

type t = (hyp * Typ_t.t option) Deque.dq
(* type t = ((string * Typ_t.t) option) Deque.dq *)
(* type t = Typ_t.t SMap.t *)
val empty : t
val ( $$ ) : t -> (hyp * Typ_t.t option) -> t
val adj : t -> (string * Typ_t.t) -> t
val adj_none : t -> string -> t
val adjs : t -> (string * Typ_t.t) list -> t
val adj_hyp : t -> Expr.T.hyp -> t * string option
val adj_hyps : t -> Expr.T.hyp Deque.dq -> t * string list
(* val adj_hyps : 'a Expr.Visit.scx -> t -> Expr.T.hyp Deque.dq -> 'a Expr.Visit.scx * t * string list *)
val ( $! ) : t -> t -> t
(* val mk : Expr.T.hyp Deque.dq -> string list * t *)
val mk : string list -> t * string list
val find : string -> t -> Typ_t.t
val pp : Format.formatter -> t -> unit
val eq : t -> t -> bool
val subst : string -> Typ_t.t -> t -> t
val vsubst : string -> string -> t -> t
(* val merge : t list -> t *)
val tyvars : t -> string list
(* val finds : t -> string list -> string list *)
val to_list : t -> (hyp * Typ_t.t option) list
val to_cx : t -> hyp list
val to_scx : t -> hyp Deque.dq
val simplify : t -> t
val ss_to_env : ty_subst list -> t
val map : (Typ_t.t -> Typ_t.t) -> t -> t

val ppt : Format.formatter -> (t * Typ_t.t) -> unit
val pp_ref : Format.formatter -> (t * Typ_t.tref) -> unit
val pp_ss : Format.formatter -> (t * Typ_t.ty_subst) -> unit
(* val fmt_expr : Expr.Fmt.ctx -> expr -> Tla_parser.Fu.exp *)
val pp_print_expr : Expr.Fmt.ctx -> Format.formatter -> expr -> unit
val pp_print_hyp : Expr.Fmt.ctx -> Format.formatter -> hyp -> Expr.Fmt.ctx
val pp_print_sequent : Expr.Fmt.ctx -> Format.formatter -> sequent -> Expr.Fmt.ctx

val ctr_types : int ref
val fresh_tyvar : ?id:string -> (hyp list * expr) -> string
