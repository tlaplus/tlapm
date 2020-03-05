#/bin/bash

ocamlopt -c fotypes.mli
ocamllex folex.mll
ocamlopt -c fofunctions.ml
ocamlyacc foyacc.mly
ocamlopt -c foyacc.mli
ocamlopt -c folex.ml
ocamlopt -c foyacc.ml
ocamlopt -c main.ml

ocamlopt -ccopt -static -o translate.static.bin fofunctions.cmx folex.cmx foyacc.cmx main.cmx 
strip translate.static.bin
cp translate.static.bin fotranslate.static.bin
