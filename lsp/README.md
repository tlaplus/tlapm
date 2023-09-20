# LSP interface to the TLAPS

The `tlapm_lsp` works as an adapter between the `tlapm` and code editors, e.g., VSCode.
It is responsible for:
  - Parsing the document structure to locate features related to proofs, e.g.:
      - proof obligation by cursor position, possibly collecting all the subtree of obligations.
      - TODO: Folding of proofs.
  - Running the `tlapm` on specific obligations and reporting the results.
  - TODO: Proof re-numbering.
  - TODO: Proof decomposition.
  - TODO: Easier experimentation on missing facts.

The test folder contains a VSCode extension / LSP client. It is meant only for testing,
the real integration should be done in the TLA+ VSCode extension.
