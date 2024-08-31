#/bin/bash

ocamlopt -c fotypes.mli
ocamllex folex.mll
ocamlopt -c fofunctions.ml
ocamlyacc foyacc.mly
ocamlopt -c foyacc.mli
ocamlopt -c folex.ml
ocamlopt -c foyacc.ml
ocamlopt -c main.ml

ocamlopt -o translate.bin fofunctions.cmx folex.cmx foyacc.cmx main.cmx
strip translate.bin
cp translate.bin fotranslate.bin
