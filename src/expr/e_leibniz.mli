
(*
 * expr/lebniz.ml --- detect leibniz positions in operators
 *
 *
 * Copyright (C) 2008-2014  INRIA and Microsoft Corporation
 *)

open E_t
open E_visit


val is_leibniz: 'a Property.wrapped -> int -> bool

class virtual leibniz_visitor: object
  inherit [unit] E_visit.map
  method expr     : unit scx -> expr -> expr
  method pform    : unit scx -> pform -> pform
  method sel      : unit scx -> sel -> sel
  method sequent  : unit scx -> sequent -> unit scx * sequent
  method defn     : unit scx -> defn -> defn
  method defns    : unit scx -> defn list -> unit scx * defn list
  method bounds   : unit scx -> bound list -> unit scx * bound list
  method bound    : unit scx -> bound -> unit scx * bound
  method exspec   : unit scx -> exspec -> exspec
  method instance : unit scx -> instance -> instance
  method hyp      : unit scx -> hyp -> unit scx * hyp
  method hyps     : unit scx -> hyp Deque.dq -> unit scx * hyp Deque.dq
end
