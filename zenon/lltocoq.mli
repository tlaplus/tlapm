(*  Copyright 2004 INRIA  *)

val output :
  out_channel ->
  Phrase.phrase list ->
  Phrase.phrase list ->
  Llproof.proof ->
    string list
;;

val p_expr : out_channel -> Expr.expr -> unit;;
