(*
 * Copyright (C) 2011-2019  INRIA and Microsoft Corporation
 *)

module T : sig
  open Property
  open Util
  open Expr.T
  open Proof.T
  type mule = mule_ wrapped
  and mule_ = {
    name              : hint ;
    extendees         : hints ;
    instancees        : hints ;
      (* only external instancees *)
    body              : modunit list ;
    defdepth          : int ;
    mutable stage     : stage ;
    mutable important : bool
  }
  and modunit = modunit_ wrapped
  and modunit_ =
    | Constants  of (hint * shape) list
    | Recursives of (hint * shape) list
    | Variables  of hints
    | Definition of defn * wheredef * visibility * export
    | Axiom      of hint option * expr
    | Theorem    of hint option * sequent * int * proof * proof * summary
    | Submod     of mule
    | Mutate     of [`Use of bool | `Hide] * usable
    | Anoninst   of instance * export
  and named = Named | Anonymous
  and summary = {
    sum_total      : int ;
    sum_absent     : int * Loc.locus list ;
    sum_omitted    : int * Loc.locus list ;
    sum_suppressed : int * Loc.locus list ;
  }
  and stage =
    | Special
    | Parsed | Flat
    | Final of final
  and final = { final_named  : modunit list
              ; final_obs    : obligation array
              ; final_status : status * summary
              }
  and status =
    | Unchecked | Proved | Certified | Incomplete
  type modctx = mule Coll.Sm.t
  val empty_summary: summary
  val cat_summary: summary -> summary -> summary
  val hyps_of_modunit: modunit -> Expr.T.hyp_ Property.wrapped list
  val hyp_size: modunit -> int
  val salt_prop: unit Property.pfuncs
end

module Fmt : sig
  open Ctx
  open T
  val pp_print_modunit :
    ?force:bool -> Expr.Fmt.ctx -> Format.formatter -> modunit -> Expr.Fmt.ctx
  val pp_print_module :
    ?force:bool -> Expr.Fmt.ctx -> Format.formatter -> mule -> unit
  val pp_print_modctx: Format.formatter -> modctx -> unit
  val summary: mule -> unit
end

module Standard : sig
  open T
  val tlapm       : mule
  val naturals    : mule
  val integers    : mule
  val reals       : mule
  val sequences   : mule
  val tlc         : mule
  val initctx  : modctx
end

module Gen : sig
  open Proof.T
  open T
  val generate : Expr.T.hyp Deque.dq -> mule -> mule * obligation list * summary
  val collect_usables : mule -> usable option
end

module Flatten : sig
  val flatten :
    T.modctx -> T.mule -> Util.Coll.Ss.t ->
      (T.mule_ Property.wrapped * Util.Coll.Ss.t)
end

module Elab : sig
  open Deque
  open Expr.T

  open T

  val normalize :
    modctx -> Expr.T.hyp Deque.dq -> mule -> modctx * mule * summary
end

module Dep : sig
  open Util.Coll

  val external_deps : T.mule_ Property.wrapped ->
    Hs.t * Hs.t * T.mule Sm.t
  val schedule: T.modctx -> T.modctx * T.mule list
end

module Save : sig
  open T
  type module_content = Channel of in_channel | String of string | Filesystem
  val module_content_prop: module_content Property.pfuncs
  val parse_file    : ?clock:Timing.clock -> Util.hint -> mule
  val store_module  : ?clock:Timing.clock -> mule -> unit
  val complete_load : ?clock:Timing.clock -> ?root:string -> modctx -> modctx
end

module Parser : sig
  open Tla_parser
  open T
  val parse : mule lprs
end

module Globalness : sig
  open T
  val is_global : 'a Property.wrapped -> bool
  val globalness : mule -> mule
end

module Subst : sig
    open Expr.Subst

    open T

    val app_modunits: sub -> modunit list -> sub * modunit list
    val app_modunit: sub -> modunit -> sub * modunit
    val app_mule: sub -> mule -> mule
end

module Visit : sig
    open Expr.T
    open Proof.T
    open Util

    open T

    class map : object
        method module_units: Expr.T.ctx -> modunit list ->
            ctx * modunit list
        method module_unit: ctx -> modunit ->
            ctx * modunit
        method constants: ctx -> (hint * shape) list ->
            ctx * modunit_
        method variables: ctx -> hints ->
            ctx * modunit_
        method recursives: ctx -> (hint * shape) list ->
            ctx * modunit_
        method definition: ctx -> defn -> wheredef -> visibility -> export ->
            ctx * modunit_
        method axiom: ctx -> hint option -> expr ->
            ctx * modunit_
        method theorem:
            ctx -> hint option -> sequent -> int -> proof -> proof -> summary ->
            ctx * modunit_
        method submod: ctx -> mule ->
            ctx * modunit_
        method mutate: ctx -> [`Use of bool | `Hide] -> usable ->
            ctx * modunit_
        method anoninst: ctx -> Expr.T.instance -> export ->
            ctx * modunit_
        method tla_module:
            ctx -> mule -> ctx * mule
        method tla_module_root:
            mule -> mule
        method tla_modules:
            ctx -> mule list -> ctx * mule list
        method tla_modules_root:
            mule list -> mule list
    end
end
