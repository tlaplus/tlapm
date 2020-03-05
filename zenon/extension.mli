(*  Copyright 2004 INRIA  *)

type translator =
    (Expr.expr -> Expr.expr) ->
    Mlproof.proof ->
    (Llproof.prooftree * Expr.expr list) array ->
    Llproof.prooftree * Expr.expr list
;;

type t = {
  name : string;
  newnodes :
    Expr.expr ->
    Expr.goalness ->
    (Expr.expr * Expr.goalness) list ->
      Node.node_item list;
  make_inst : Expr.expr -> Expr.expr -> Expr.goalness -> Node.node list;
  add_formula : Expr.expr -> unit;
  remove_formula : Expr.expr -> unit;
  preprocess : Phrase.phrase list -> Phrase.phrase list;
  add_phrase : Phrase.phrase -> unit;
  postprocess : Llproof.proof -> Llproof.proof;
  to_llproof : translator;
  declare_context_coq : out_channel -> unit;
  p_rule_coq : out_channel -> Llproof.rule -> unit;
  predef : unit -> string list;
};;

val register : t -> unit;;
val activate : string -> unit;;

val is_active: string -> bool;;

val newnodes :
  Expr.expr ->
  Expr.goalness ->
  (Expr.expr * Expr.goalness) list ->
    Node.node_item list list
;;
val make_inst :
  string -> Expr.expr -> Expr.expr -> Expr.goalness -> Node.node list
;;
val add_formula : Expr.expr -> unit;;
val remove_formula : Expr.expr -> unit;;
val preprocess : Phrase.phrase list -> Phrase.phrase list;;
val add_phrase : Phrase.phrase -> unit;;
val postprocess : Llproof.proof -> Llproof.proof;;
val to_llproof : translator;;
val declare_context_coq : out_channel -> unit;;
val p_rule_coq : string -> out_channel -> Llproof.rule -> unit;;
val predef : unit -> string list;;

val memorec : ((Expr.expr -> 'a) -> Expr.expr -> 'a) -> Expr.expr -> 'a
