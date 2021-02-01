(*
 * type/recon.mli --- decorate TLA+ expressions with types
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open Util

open T_t

(** This module implements Type Reconstruction for non-temporal expressions.
    
    TR will decorate expressions with type annotations.  The expressions
    themselves are not modified.  See {!Type.T} for a presentation of the type
    system and the relevant annotations.

    Annotations are placed in different places.
    - All {!Util.hint} may receive a {!Type.T.ty0_prop}, {!Type.T.ty1_prop} or a
      {!Type.T.ty2_prop} annotation.  The last two are reserved for operator
      variables (on fresh variables, defined operators, arguments to second-
      order lambda-terms).
    - Many TLA+ builtins exist in an untyped version (actually a typed version
      that used the idv sort exclusively), and a number of typed version.
      Expressions built from the constructor {!Expr.T.Internal} may receive the
      annotation {!Type.T.tpars_prop} to indicate which type version is the
      correct one.  No annotation means untyped version.
    - For TLA+ primitives that do not have a builtin, like {!Expr.T.SetSt}, the
      annotation is placed on the expression itself.
    - Bounds imply a hidden [\in].  The optional annotation for it may be found
      on the domain of the bound.
    - Some expressions must be cast from some type [ty] to the domain of
      individuals.  The annotation {!Type.T.icast_prop} with parameter [ty]
      decorates these expressions.
    - Some expressions must be projected from some type [ty] into the domain of
      booleans.  The annotation {!Type.T.bproj_prop} with parameter [ty]
      decorates these expressions.

    Some flags affect type reconstruction.
    - {!Params.enc_typelvl} determines how much of the type system is used.
      - If typelvl=0 then [idv] is used for most expressions; [int] is used for
        arithmetic expressions; [bool] is used for formulas, but be aware that
        most TLA+ operators are not interpreted as predicates, for instance \in
        is not guaranteed to return a boolean, therefore it is not encoded as a
        predicate.
      - If typelvl=1 then set-types, function-types, etc. may be used.
        TODO actually implement
    - {!Params.enc_typepreds} allows \in to be encoded as a predicate.  Another
      example is the SetSt constructor, which will expect a predicate argument
      if the flag is set.  This flag is independent of the typelvl flag.

  NOTE This module is based on the liberal interpretation of TLA+ for formulas!
*)


(* {3 Context} *)

type scx

val init : scx

val adj_ty0 : scx -> hint -> ty0 -> hint * scx
val adj_ty1 : scx -> hint -> ty1 -> hint * scx
val adj_ty2 : scx -> hint -> ty2 -> hint * scx

val bump : scx -> scx

val lookup_ty0 : scx -> int -> ty0
val lookup_ty1 : scx -> int -> ty1
val lookup_ty2 : scx -> int -> ty2


(* {3 Main} *)

val expr : scx -> expr -> expr * ty0  (** Called on constant expressions *)
val earg : scx -> expr -> expr * ty1  (** Called on application arguments *)
val eopr : scx -> expr -> expr * ty2  (** Called on applied operators *)

(** @param ignore disables parsing, infers a generic type from the shape *)
val defn  : ?ignore:bool -> scx -> defn -> scx * defn
val defns :                 scx -> defn list -> scx * defn list

val hyp  : scx -> hyp -> scx * hyp
val hyps : scx -> hyp Deque.dq -> scx * hyp Deque.dq

val sequent : scx -> sequent -> scx * sequent

val main : sequent -> sequent

