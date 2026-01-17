all: test

build:
	dune build

test: build
	dune test

test-verbose: build
	(cd ../../_build/default/lsp/test; ./tlapm_lsp_test.exe --verbose)

