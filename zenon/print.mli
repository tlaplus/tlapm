(*  Copyright 2004 INRIA  *)

type output = Buff of Buffer.t | Chan of out_channel;;

val expr : output -> Expr.expr -> unit;;
val expr_soft : output -> Expr.expr -> unit;;

val phrase : output -> Phrase.phrase -> unit;;

val hlproof : output -> int -> Mlproof.proof -> unit;;

val mlproof : output -> Mlproof.proof -> unit;;
val mlproof_rule : output -> Mlproof.rule -> unit;;
val mlproof_rule_soft : output -> Mlproof.rule -> unit;;

val llproof : output -> Llproof.proof -> unit;;
