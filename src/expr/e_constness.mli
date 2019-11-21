(*
 * expr/constness.ml --- detect constant operators
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open E_t
open E_visit

(* returns the const value of the term *)
val is_const : 'a Property.wrapped -> bool
(* checks if const was already computed for this term *)
val has_const : 'a Property.wrapped -> bool

class virtual const_visitor : object
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
