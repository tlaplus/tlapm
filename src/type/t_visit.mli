(*
 * type/visit.mli --- visitors with syntactic typechecking
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open T_t

type 's scx = 's * hyp Deque.dq

val adj  : 's scx -> hyp -> 's scx
val adjs : 's scx -> hyp list -> 's scx

val lookup_ty0 : 's scx -> int -> ty0
val lookup_ty1 : 's scx -> int -> ty1
val lookup_ty2 : 's scx -> int -> ty2

(* FIXME implement map, iter and fold *)

class virtual ['s, 'a] foldmap : object
  method expr     : 's scx -> 'a -> expr -> 'a * expr * ty0
  method earg     : 's scx -> 'a -> expr -> 'a * expr * ty1
  method eopr     : 's scx -> 'a -> expr -> 'a * expr * ty2
  method pform    : 's scx -> 'a -> pform -> 'a * pform
  method sel      : 's scx -> 'a -> sel -> 'a * sel
  method sequent  : 's scx -> 'a -> sequent -> 's scx * 'a * sequent
  method defn     : 's scx -> 'a -> defn -> 'a * defn
  method defns    : 's scx -> 'a -> defn list -> 's scx * 'a * defn list
  method bounds   : 's scx -> 'a -> bound list -> 's scx * 'a * bound list
  method bound    : 's scx -> 'a -> bound -> 's scx * 'a * bound
  method exspec   : 's scx -> 'a -> exspec -> 'a * exspec * ty0 list
  method instance : 's scx -> 'a -> instance -> 'a * instance
  method hyp      : 's scx -> 'a -> hyp -> 's scx * 'a * hyp
  method hyps     : 's scx -> 'a -> hyp Deque.dq -> 's scx * 'a * hyp Deque.dq
end

