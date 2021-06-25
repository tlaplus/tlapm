(* Copyright (C) 2011-2012  INRIA and Microsoft Corporation *)
open Expr.T

val prepreproc : sequent -> sequent
val skolemize : sequent -> sequent
val simpl_eq : unit Expr.Visit.scx -> (expr list * expr) -> (expr list * expr)
val abstract : unit Expr.Visit.scx -> (expr list * expr) -> (expr list * expr)
val abstract2 : unit Expr.Visit.scx -> (expr list * expr) -> (expr list * expr)
