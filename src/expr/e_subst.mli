(*
 * expr/subst.ml --- substitutions
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Property
open E_t

type sub

val shift : int -> sub
val scons : expr -> sub -> sub
val ssnoc : sub -> expr -> sub
val compose : sub -> sub -> sub

val bumpn : int -> sub -> sub
val bump : sub -> sub
val app_ix : sub -> int wrapped -> expr
val normalize : ?cx:hyp Deque.dq -> expr -> expr list -> expr_
val app_expr : sub -> expr -> expr
val app_exprs : sub -> expr list -> expr list
val app_sel : sub -> sel -> sel
val app_bdom : sub -> bound_domain -> bound_domain
val app_bound : sub -> bound -> sub * bound
val app_bounds : sub -> bound list -> sub * bound list
val app_defn : sub -> defn -> defn
val app_defns : sub -> defn list -> sub * defn list
val app_instance : sub -> instance -> instance
val app_sequent : sub -> sequent -> sequent
val app_hyps : sub -> hyp Deque.dq -> sub * hyp Deque.dq
val app_hyp : sub -> hyp -> hyp
val app_spine : sub -> expr list -> expr list

val extract : sequent -> int -> (sequent * expr) option

val pp_print_sub : E_fmt.ctx -> Format.formatter -> sub -> unit
