(*
 * Copyright (C) 2014  INRIA and Microsoft Corporation
 *)

open Expr.T
open Expr.Visit

module OrderedSymbol :
  sig type t = expr val compare : expr -> expr -> int
end

module SymbolMap : Map.S with type key = OrderedSymbol.t

val symbol_commute : (unit Expr.Visit.map * (expr -> expr)) SymbolMap.t -> expr -> expr;;

