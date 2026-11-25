module TL := Tlapm_lib
module LspT := Util.LspT

val code_actions :
  cfg:Config.t ->
  Docs.tk ->
  Docs.Proof_step.t ->
  Docs.Proof_step.t ->
  TL.Expr.T.ctx ->
  LspT.CodeAction.t list
