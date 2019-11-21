

(*
 *A set of normalization functions for expanding TLA built-in formulas

 * Copyright (C) 2013  INRIA and Microsoft Corporation
 *)

val expand_unchanged : unit E_visit.scx -> E_t.expr -> E_t.expr
val expand_action : unit E_visit.scx -> E_t.expr -> E_t.expr
val expand_leadsto : unit E_visit.scx -> E_t.expr -> E_t.expr
val expand_fairness : unit E_visit.scx -> E_t.expr -> E_t.expr
