
(*
 * Coalescing transforms a formula to a satisfying-equiavelnt formula.
   *  coalsecing non-leibzniz formulas into leibniz formulas. The resuled
   * formulas can then be used in first-order theorem provers.
 *
 * Copyright (C) 2013  INRIA and Microsoft Corporation
 *)

val coalesce : Expr.T.hyp Deque.dq -> Expr.T.expr -> Expr.T.expr
val coalesce_modal : Expr.T.expr -> Expr.T.expr
