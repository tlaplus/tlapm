module TL := Tlapm_lib
module LspT := Util.LspT

val cas_def_expand :
  uri:Docs.tk ->
  ps:Docs.Proof_step.t ->
  cx:TL.Expr.T.hyp TL.Util.Deque.dq ->
  by:TL.Proof.T.usable * bool ->
  sq:TL.Expr.T.sequent ->
  LspT.CodeAction.t list
