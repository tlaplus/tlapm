(* https://github.com/tlaplus/tlaplus/blob/master/toolbox/org.lamport.tla.toolbox.editor.basic/src/org/lamport/tla/toolbox/editor/basic/handlers/DecomposeProofHandler.java *)
module LspT := Lsp.Types

val code_actions :
  LspT.DocumentUri.t -> Docs.Proof_step.t -> Range.t -> LspT.CodeAction.t list
