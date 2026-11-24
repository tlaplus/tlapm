(*
 * Copyright (C) 2014  INRIA and Microsoft Corporation
 *)

open Expr.T
open Expr.Visit

module OrderedSymbol :
  sig type t = expr val compare : expr -> expr -> int
end

module SymbolMap : Map.S with type key = OrderedSymbol.t

(* Each commuter receives the initial hypothesis-context size as its state. *)
val symbol_commute : (int Expr.Visit.map * (expr -> expr)) SymbolMap.t -> expr -> expr;;

