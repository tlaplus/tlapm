module LspT := Lsp.Types

val code_actions :
  LspT.DocumentUri.t -> Docs.Proof_step.t -> Range.t -> LspT.CodeAction.t list
