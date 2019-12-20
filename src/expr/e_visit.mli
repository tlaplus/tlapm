(*
 * expr/visit.mli --- default visitor for expressions
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open E_t

val hyp_rename : Util.hint -> hyp -> hyp

type 's scx = 's * hyp Deque.dq

val adj  : 's scx -> hyp -> 's scx
val adjs : 's scx -> hyp list -> 's scx

class virtual ['s] map : object
  method expr     : 's scx -> expr -> expr
  method pform    : 's scx -> pform -> pform
  method sel      : 's scx -> sel -> sel
  method sequent  : 's scx -> sequent -> 's scx * sequent
  method defn     : 's scx -> defn -> defn
  method defns    : 's scx -> defn list -> 's scx * defn list
  method bounds   : 's scx -> bound list -> 's scx * bound list
  method bound    : 's scx -> bound -> 's scx * bound
  method exspec   : 's scx -> exspec -> exspec
  method instance : 's scx -> instance -> instance
  method hyp      : 's scx -> hyp -> 's scx * hyp
  method hyps     : 's scx -> hyp Deque.dq -> 's scx * hyp Deque.dq
end

class virtual ['s] iter : object
  method expr     : 's scx -> expr -> unit
  method pform    : 's scx -> pform -> unit
  method sel      : 's scx -> sel -> unit
  method sequent  : 's scx -> sequent -> 's scx
  method defn     : 's scx -> defn -> 's scx
  method defns    : 's scx -> defn list -> 's scx
  method bounds   : 's scx -> bounds (*list*) -> 's scx
  method bound    : 's scx -> bound -> 's scx
  method exspec   : 's scx -> exspec -> unit
  method instance : 's scx -> instance -> unit
  method hyp      : 's scx -> hyp -> 's scx
  method hyps     : 's scx -> hyp Deque.dq -> 's scx
end

class virtual ['s, 'a] foldmap : object
  method expr     : 's scx -> 'a -> expr -> 'a * expr
  method pform    : 's scx -> 'a -> pform -> 'a * pform
  method sel      : 's scx -> 'a -> sel -> 'a * sel
  method sequent  : 's scx -> 'a -> sequent -> 's scx * 'a * sequent
  method defn     : 's scx -> 'a -> defn -> 'a * defn
  method defns    : 's scx -> 'a -> defn list -> 's scx * 'a * defn list
  method bounds   : 's scx -> 'a -> bound list -> 's scx * 'a * bound list
  method bound    : 's scx -> 'a -> bound -> 's scx * 'a * bound
  method exspec   : 's scx -> 'a -> exspec -> 'a * exspec
  method instance : 's scx -> 'a -> instance -> 'a * instance
  method hyp      : 's scx -> 'a -> hyp -> 's scx * 'a * hyp
  method hyps     : 's scx -> 'a -> hyp Deque.dq -> 's scx * 'a * hyp Deque.dq
end

class virtual ['s, 'a] fold : object
  method expr     : 's scx -> 'a -> expr -> 'a
  method pform    : 's scx -> 'a -> pform -> 'a
  method sel      : 's scx -> 'a -> sel -> 'a
  method sequent  : 's scx -> 'a -> sequent -> 's scx * 'a
  method defn     : 's scx -> 'a -> defn -> 'a
  method defns    : 's scx -> 'a -> defn list -> 's scx * 'a
  method bounds   : 's scx -> 'a -> bound list -> 's scx * 'a
  method bound    : 's scx -> 'a -> bound -> 's scx * 'a
  method exspec   : 's scx -> 'a -> exspec -> 'a
  method instance : 's scx -> 'a -> instance -> 'a
  method hyp      : 's scx -> 'a -> hyp -> 's scx * 'a
  method hyps     : 's scx -> 'a -> hyp Deque.dq -> 's scx * 'a
end
