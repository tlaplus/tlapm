#/bin/bash

ocamlc -c fotypes.mli
ocamllex folex.mll
ocamlc -c fofunctions.ml
ocamlyacc foyacc.mly
ocamlc -c foyacc.mli
ocamlc -c folex.ml
ocamlc -c foyacc.ml
ocamlc -c main.ml

ocamlc -o translate fofunctions.cmo folex.cmo foyacc.cmo main.cmo
cp translate fotranslate
