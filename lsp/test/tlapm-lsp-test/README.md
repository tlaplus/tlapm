# Test TLAPM plugin

It is here only to test some `tlapm_lsp` functions.
The real plugin should be part of the TLA+ vscode extension.

To use this plugin:
  - Assuming `lsp/test/tlapm-lsp-test` as the current directory.
  - Build and install the backend with `make -C ../../../ build install`
  - Open `.` in the VSCode, e.g. `code .`
  - Press `F5` (Run -> Run and debug),
      - New window has this plugin launched.
      - Backend log is in the file `./tlapm_lsp.log`.
