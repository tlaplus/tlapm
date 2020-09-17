(*
 * type/bool.mli --- sort formulas and non-formulas
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** TLA+ expressions are untyped to the extent that the traditionnal
    distinction between formulas and non-formulas does not exist.  This module
    implements a simple algorithm that inserts casts from Bool to Idv (the sort
    of all expressions) and projections from Idv to Bool in order to make any
    expression well-typed wrt Bool and Idv.

    A cast into Idv is just a property {!Type.T.icast_prop} attached to an
    expression.  A projection into Bool is represented by the property
    {!Type.T.bproj}.  Projecting is not injective like casting; projecting [e]
    into Bool can be understood as rewriting [e] as [e = TRUE].

    The algorithm also decorates bound variables and declared operators with
    type annotations.  The only types used are Idv and Bool.
*)

(* NOTE The whole signature is shown for documentation, but you should only
 * use {!Type.Bool.main}. *)

open Expr.T
open Type.T

open Ext
open Util


(* {3 Context} *)

(** The three types below are only used internally *)
type srt = Idv | Bool
type ty1 = Ty1 of srt list * srt
type ty2 = Ty2 of ty1 list * srt

type scx (* Hidden *)

val init : scx

val adj_srt : scx -> hint -> srt -> hint * scx
val adj_ty1 : scx -> hint -> ty1 -> hint * scx
val adj_ty2 : scx -> hint -> ty2 -> hint * scx

val bump : scx -> scx

val lookup_srt : scx -> int -> srt
val lookup_ty1 : scx -> int -> ty1
val lookup_ty2 : scx -> int -> ty2


(* {3 Main} *)

val mk_idv  : srt -> expr -> expr
val mk_bool : srt -> expr -> expr

val expr : scx -> expr -> expr * srt  (** Called on constant expressions *)
val earg : scx -> expr -> expr * ty1  (** Called on application arguments *)
val eopr : scx -> expr -> expr * ty2  (** Called on applied operators *)

val bound  : scx -> bound -> bound
val bounds : scx -> bound list -> scx * bound list

val hdefn : scx -> defn -> scx * defn (* Call on hidden defns *)
val defn  : scx -> defn -> scx * defn
val defns : scx -> defn list -> scx * defn list

val hyp  : scx -> hyp -> scx * hyp
val hyps : scx -> hyp Deque.dq -> scx * hyp Deque.dq

val sequent : scx -> sequent -> scx * sequent

(** Main function.
    @param hidden Also parse hidden facts and defns (default=false);
    @param bunify Allow equality on Bool and ite with
           Bool branches (default=true);
    @param ccast Constants of a type other than
           Idv or Bool casted to Idv (default=true);
    @param tpred Type inference on definitions (default=false).
*)
val main :
  ?hidden:bool ->
  ?bunify:bool ->
  ?ccast:bool ->
  ?tpred:bool ->
    sequent -> sequent

