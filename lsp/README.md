# LSP interface to the TLAPS

The `tlapm_lsp` works as an adapter between the `tlapm` and code editors, e.g., VSCode.
It is responsible for:
  - Parsing the document structure to locate features related to proofs, e.g.:
      - proof obligation by cursor position, possibly collecting all the subtree of obligations.
  - Running the `tlapm` on specific obligations and reporting the results.
  - TODO: Proof re-numbering.
  - TODO: Proof decomposition.
  - TODO: Easier experimentation on missing facts.

The test folder contains a VSCode extension / LSP client. It is meant only for testing,
the real integration should be done in the TLA+ VSCode extension.

See:
  - Dafny plugin. It shows all the obligations as testcases.
    <https://github.com/dafny-lang/ide-vscode>
    <https://github.com/dafny-lang/dafny/tree/master/Source/DafnyLanguageServer>
  - VSCode Decorators: https://github.com/microsoft/vscode-extension-samples/blob/main/decorator-sample/README.md
    https://vscode.rocks/decorations/
    Gutter -- the left side of the editor.

