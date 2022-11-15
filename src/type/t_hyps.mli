(*
 * type/hyps.mli --- search for type hypotheses
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T

open T_t

type scx = hyp Deque.dq

(** Suppose [e] is an expression in the context [scx, NEW x].
    If [search_type_hyp ~inferer ~pol:true scx e] returns some [ty], then:

      [scx, NEW x |= P_ty(x) \/ e]

    where [P_ty] is the type predicate of [ty].  This implies that:

      [scx, NEW x |= e <=> ( P_ty(x) => e )]

    which means that the type [ty] can be safely assumed for [x].

    Setting [pol] to [false] amounts to call the function on [~ e] instead,
    and can be used to find type hypotheses for existentials.
*)
val search_type_hyp :
  inferer:(scx -> expr -> ty0) ->
  pol:bool ->
  scx -> expr -> ty0 option

