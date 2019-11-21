(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

module T : sig
  open Property;;
  open Util;;
  open Expr.T;;
  open Proof.T;;
  type mule = mule_ wrapped
  and mule_ = {
    name              : hint ;
    extendees         : hint list ;
    instancees        : hint list ;
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
    | Variables  of hint list
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
  ;;
  type modctx = mule Coll.Sm.t;;
  val empty_summary : summary;;
  val cat_summary : summary -> summary -> summary;;
  val hyps_of_modunit : modunit -> Expr.T.hyp_ Property.wrapped list;;
  val hyp_size : modunit -> int;;
  val salt_prop : unit Property.pfuncs;;
end;;

module Fmt : sig
  open Ctx
  open T
  val pp_print_modunit :
    ?force:bool -> Expr.Fmt.ctx -> Format.formatter -> modunit -> Expr.Fmt.ctx
  ;;
  val pp_print_module :
    ?force:bool -> Expr.Fmt.ctx -> Format.formatter -> mule -> unit
  ;;
  val pp_print_modctx : Format.formatter -> modctx -> unit;;
  val summary : mule -> unit;;
end;;

module Standard : sig
  open T
  val tlapm       : mule
  val naturals    : mule
  val integers    : mule
  val reals       : mule
  val sequences   : mule
  val tlc         : mule
  val initctx  : modctx
end;;

module Gen : sig
  open Proof.T
  open T
  val generate : Expr.T.hyp Deque.dq -> mule -> mule * obligation list * summary
  val collect_usables : mule -> usable option
end;;

module Flatten : sig
  val flatten :
    T.modctx -> T.mule -> Util.Coll.Ss.t ->
      (T.mule_ Property.wrapped * Util.Coll.Ss.t)
  ;;
end;;

module Elab : sig
  open Proof.T
  open T
  val normalize :
    modctx -> Expr.T.hyp Deque.dq -> mule -> modctx * mule * summary
  ;;
end;;

module Dep : sig
  val external_deps : T.mule_ Property.wrapped -> Util.Coll.Hs.t;;
  val schedule : T.modctx -> T.modctx * T.mule list;;
end;;

module Save : sig
  open T
  val parse_file    : ?clock:Timing.clock -> Util.hint -> mule
  val store_module  : ?clock:Timing.clock -> mule -> unit
  val complete_load : ?clock:Timing.clock -> ?root:string -> modctx -> modctx
end;;

module Parser : sig
  open Tla_parser
  open T
  val parse : mule lprs
end;;

module Globalness : sig
  open T
  val is_global : 'a Property.wrapped -> bool
  val globalness : mule -> mule
end;;
