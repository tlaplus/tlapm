(lang dune 3.7)

(using dune_site 0.1)

(using directory-targets 0.1)

(name tlapm)

(generate_opam_files true)

(source (github tlaplus/tlapm))

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
 (depends ocaml dune-site))

; TODO: https://github.com/ocaml/dune/tree/main/example/with-configure-step.t
;       to derive the current os to name the release?
