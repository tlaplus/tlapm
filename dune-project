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
 (sites (lib backends)) ; will contain all the provers, approx lib/tlapm/backends/.
 (depends ocaml dune))
