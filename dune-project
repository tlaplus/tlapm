(lang dune 3.7)

(using directory-targets 0.1)

(name tlapm)

(generate_opam_files true)

(source (github tlaplus/tlapm))

(package
 (name tlapm)
 (synopsis "TLA+ Proof Manager")
 (description "TLA+ Proof Manager")
 (depends ocaml dune))
