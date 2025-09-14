(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)
module T : sig
  open Property
  open Expr.T
  type omission =
    | Implicit
    | Explicit
    | Elsewhere of Loc.locus
  type proof = proof_ wrapped
  and proof_ =
    | Obvious
    | Omitted of omission
    | By      of usable * bool
    | Steps   of step list * qed_step
    | Error   of string
  and step = step_ wrapped
  and step_ =
    | Hide     of usable
    | Define   of defn list
    | Assert   of sequent * proof
    | Suffices of sequent * proof
    | Pcase    of expr * proof
    | Pick     of bound list * expr * proof
    | PickTuply of tuply_bounds * expr * proof
    | Use      of usable * bool
    | Have     of expr
    | Take     of bound list
    | TakeTuply of tuply_bounds
    | Witness  of expr list
    | Forget   of int
  and qed_step = qed_step_ wrapped
  and qed_step_ =
    | Qed of proof
  and usable = { facts : expr list
               ; defs  : use_def wrapped list }
  and use_def =
    | Dvar of string
    | Dx   of int
  type obligation_kind =
    | Ob_main
    | Ob_support
    | Ob_error of string
    | Ob_omitted of omission
  type obligation = {
    id  : int option;
    obl : sequent wrapped;
    fingerprint : string option;
    kind : obligation_kind;
  }
  type stepno =
    | Named   of int * string * bool
    | Unnamed of int * int
    [@@deriving show]
  module Props : sig
    val step : stepno Property.pfuncs
    val goal : sequent pfuncs
    val supp : unit pfuncs
    val obs : obligation list pfuncs
    val meth : Method.t list pfuncs
    val orig_step : step Property.pfuncs
    val orig_proof : proof Property.pfuncs
    val use_location : Loc.locus Property.pfuncs
  end
  val string_of_stepno: ?anonid:bool -> stepno -> string
  val get_qed_proof: qed_step_ Property.wrapped -> proof
  val step_number: stepno -> int
end

module Fmt : sig
  open Ctx
  open T
  val pp_print_obligation : Format.formatter -> obligation -> unit
  val pp_print_proof : Expr.Fmt.ctx -> Format.formatter -> proof -> unit
  val pp_print_step : Expr.Fmt.ctx -> Format.formatter -> step -> Expr.Fmt.ctx
  val pp_print_usable : Expr.Fmt.ctx -> Format.formatter -> usable -> unit
  val string_of_step : Expr.T.hyp Deque.dq  -> step -> string
end

module Subst : sig
  open Expr.Subst
  open T
  val app_proof : sub -> proof -> proof
  val app_step : sub -> step -> sub * step
  val app_inits : sub -> step list -> sub * step list
  val app_usable : sub -> usable -> usable
end

module Visit : sig
  open Deque
  open Expr.T
  open T
  open Expr.Visit
  val bump : 's scx -> int -> 's scx
  class virtual ['s] map : object
    inherit ['s] Expr.Visit.map
    method proof  : 's scx -> proof -> proof
    method steps  : 's scx -> step list -> 's scx * step list
    method step   : 's scx -> step -> 's scx * step
    method usable : 's scx -> usable -> usable
  end
  class virtual ['s] iter : object
    inherit ['s] Expr.Visit.iter
    method proof  : 's scx -> proof -> unit
    method steps  : 's scx -> step list -> 's scx
    method step   : 's scx -> step -> 's scx
    method qed    : 's scx -> qed_step -> unit
    method usable : 's scx -> usable -> unit
  end
end

module Simplify : sig
  open Property
  open Deque
  open Expr.T
  open T
  val simplify : hyp dq -> expr -> proof -> time -> proof
end

module Anon : sig
  class anon : [string list] Visit.map
  val anon : anon
end

module Gen : sig
  open Deque
  open Property
  open Expr.T
  open T
  val prove_assertion :
    suffices:bool ->
    hyp dq -> expr -> sequent wrapped -> time -> hyp dq * expr * time
  val use_assertion :
    suffices:bool ->
    hyp dq -> expr -> sequent wrapped -> time -> hyp dq * expr
  val get_steps_proof : proof -> step list
  val generate : sequent -> proof -> time -> proof
  val collect  : proof -> obligation list * proof
  val mutate : hyp Deque.dq ->
    [`Use of bool | `Hide] -> usable wrapped -> time -> hyp Deque.dq * obligation list
  type stats = {
    total      : int ;
    checked    : int ;
    absent     : Loc.locus list ;
    omitted    : Loc.locus list ;
    suppressed : Loc.locus list ;
  }
  val get_stats   : unit -> stats
  val reset_stats : unit -> unit
end

module Parser : sig
  type supp = Emit | Suppress
  val qed_loc_prop : Loc.locus Property.pfuncs
  val usebody : T.usable Tla_parser.lprs
  val proof : T.proof Tla_parser.lprs
  val suppress : supp Tla_parser.lprs
end
