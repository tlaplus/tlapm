(* Copyright (C) 2011-2012  INRIA and Microsoft Corporation *)
open Expr.T

(* val gr0 : expr -> expr *)
(* val gr1 : hyp list -> expr -> expr *)
(* val unbound : hyp list -> expr -> expr *)
(* val rw : sequent -> sequent *)

class rw : object
  inherit [unit] Expr.Visit.map
  (* method expr     : unit Expr.Visit.scx -> expr -> expr
  method sequent  : unit Expr.Visit.scx -> sequent -> unit Expr.Visit.scx * sequent
  method pform    : unit Expr.Visit.scx -> pform -> pform
  method sel      : unit Expr.Visit.scx -> sel -> sel
  method defn     : unit Expr.Visit.scx -> defn -> defn
  method defns    : unit Expr.Visit.scx -> defn list -> unit Expr.Visit.scx * defn list
  method bounds   : unit Expr.Visit.scx -> bound list -> unit Expr.Visit.scx * bound list
  method bound    : unit Expr.Visit.scx -> bound -> unit Expr.Visit.scx * bound
  method exspec   : unit Expr.Visit.scx -> exspec -> exspec
  method instance : unit Expr.Visit.scx -> instance -> instance
  method hyp      : unit Expr.Visit.scx -> hyp -> unit Expr.Visit.scx * hyp
  method hyps     : unit Expr.Visit.scx -> hyp Deque.dq -> 's Expr.Visit.scx * hyp Deque.dq *)
end
