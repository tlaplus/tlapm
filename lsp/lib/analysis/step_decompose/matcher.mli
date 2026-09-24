open Tlapm_lib

type bindings

val pp_bindings : Expr.T.ctx -> bindings Fmt.t
val pp_bindings_opt : Expr.T.ctx -> bindings option Fmt.t

val match_expr :
  cx:Expr.T.ctx -> t:Expr.T.expr -> p:Expr.T.expr -> bindings option
(** [match_expr ~cx ~t ~p] tries to match target expression [~t] with the
    pattern [~p]. Both should be aligned at the top of context [~cx]. *)

val match_rule_hyps :
  cx:Expr.T.ctx ->
  t:Expr.T.sequent ->
  p:Expr.T.sequent ->
  matched:bindings ->
  bindings list
(** TODO: Cleanup this. *)

val subst_of_bindings : bindings -> Expr.Subst.sub
(** Apply this substitution to the pattern and you will get the matched AST.
    Used e.g. to apply the matches to the proof of the matched theorem/rule. *)
