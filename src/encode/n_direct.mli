(*
 * encode/direct.mli --- eliminate primitives and builtins
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open Type.T
open Util

(** The purpose of this module is to encode expressions in a fragment of the
    language that doesn't use builtins.  No prior type reconstruction needed.

    Any primitive construct is encoded as an application F(e_1,..,e_n) where
    F is an opaque symbol with an annotation {!Encode.Table.smb}.  For
    instance, "a \cup b" results in "cup(a, b)".  This applies also to second-
    order constructs: "{ x \in a : E }" results in "setst(a, LAMBDA x : E)".

    The encoding does two additional things.  One: bound variables and declared
    operators receive a type annotation.  The only base types in this module
    are Set and Bool.  Two: casts (from Bool to Set) and projections (from Set
    to Bool) are inserted, so that the resulting expression is well-typed.
    See {!Type.T.Props}.
*)


(* Signatures are given for pedagogical purposes.
 * Please only use {!Encode.Direct.main}. *)


(* {3 Context} *)

type rty = RSet | RForm                 (** Result type *)
type aty = ASet | AOp of int * rty      (** Argument type *)
type xty = XSet | XOp of aty list * rty (** Type *)

type cx = xty Ctx.t


(* {3 Main} *)

val expr : cx -> expr -> expr * rty
val eopr : cx -> expr -> expr * xty (* Called on operator in an application *)
val earg : cx -> expr -> expr * aty (* Called on args in an application *)

(* NOTE bound doesn't update cx because bounds are read in the upper context *)
val bound : cx -> bound -> bound
val bounds : cx -> bound list -> cx * bound list

val defn : cx -> defn -> cx * defn
val defns : cx -> defn list -> cx * defn list

val hyp : cx -> hyp -> cx * hyp
val hyps : cx -> hyp Deque.dq -> cx * hyp Deque.dq

val sequent : cx -> sequent -> sequent

val main : sequent -> sequent

