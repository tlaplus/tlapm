let pkgs = import <nixpkgs> {};
in pkgs.mkShell {
  packages = with pkgs; [
    # Fundamental dependencies
    bash
    ocaml                       # OCaml compiler & interpreter
    dune_3                      # OCaml build system
    gnumake                     # Called by Dune to build non-OCaml code
    ocamlPackages.findlib       # OCaml library manager

    # CLI tools necessary to build & test project
    gawk
    gnupatch
    time
    zlib

    # OCaml packages necessary to build & test project
    ocamlPackages.camlzip         # Library for handling zip & gzip files
    ocamlPackages.cmdliner        # Enables declarative CLI definitions
    ocamlPackages.eio_main        # Parallel IO library
    ocamlPackages.dune-build-info # Embed build information inside executables
    ocamlPackages.dune-site       # Embed location information inside executables
    ocamlPackages.lsp             # LSP protocol library for building LSP servers
    ocamlPackages.odoc            # Documentation generator
    ocamlPackages.ounit2          # Unit testing framework for OCaml
    ocamlPackages.ppx_assert      # Macro library for assertions with useful errors
    ocamlPackages.ppx_deriving    # Macro library for auto-displaying datatypes
    ocamlPackages.ppx_inline_test # Macro library for writing in-line tests
    ocamlPackages.re2             # Regular expression library
    ocamlPackages.sexplib         # Library for building & parsing S-expression

    # Optional packages to assist OCaml development
    ocamlPackages.earlybird       # DAP server for OCaml debugging
    ocamlPackages.ocaml-lsp       # LSP server for OCaml coding
    ocamlPackages.ocamlformat     # OCaml code formatter
    ocamlPackages.utop            # Nice OCaml REPL
  ];
}

