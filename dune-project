(lang dune 3.15)

(using dune_site 0.1)

(using directory-targets 0.1)

(name tlapm)

(generate_opam_files true)

(source (github tlaplus/tlapm))

(license BSD-2-Clause)

(cram enable)

(package
 (name tlapm)
 (synopsis "TLA+ Proof Manager")
 (description "TLA+ Proof Manager")
 (authors
  "Kaustuv Chaudhuri"
  "Denis Cousineau"
  "Damien Doligez"
  "Leslie Lamport"
  "Tomer Libal"
  "Stephan Merz"
  "Jean-Baptiste Tristan"
  "Hernan Vanzetto")
 (maintainers
  "Kaustuv Chaudhuri"
  "Denis Cousineau"
  "Damien Doligez"
  "Leslie Lamport"
  "Tomer Libal"
  "Stephan Merz"
  "Jean-Baptiste Tristan"
  "Hernan Vanzetto")
 (sites
  (lib backends) ; will contain all the provers, approx lib/tlapm/backends/.
  (lib stdlib))  ; TLA files composing the StdLib.
 (depends
  ocaml
  dune-site
  dune-build-info
  sexplib
  cmdliner
  camlzip
  re2
  ppx_inline_test
  ppx_assert
  ppx_deriving
  ounit2)
 (depopts
  lsp         ; https://github.com/ocaml/ocaml-lsp
  eio_main))  ; https://github.com/ocaml-multicore/eio, only available on OCaml version >= 5.
