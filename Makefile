OS_TYPE=$(patsubst CYGWIN%,Cygwin,$(shell uname))

ifeq ($(OS_TYPE),Linux)
	HOST_OS=linux-gnu
endif
ifeq ($(OS_TYPE),Darwin)
	HOST_OS=darwin
endif
ifeq ($(OS_TYPE),Cygwin)
	HOST_OS=cygwin
endif
HOST_CPU=$(shell uname -m)
RELEASE_NAME=tlaps-$$RELEASE_VERSION-$(HOST_CPU)-$(HOST_OS)
RELEASE_FILE=$(RELEASE_NAME).tar.gz

PREFIX=$(OPAM_SWITCH_PREFIX)

all: build

opam-update: # Update the package lists and install updates.
	opam update
	opam upgrade

opam-deps:
	opam install ./ --deps-only --yes --working-dir

opam-deps-dev:
	opam install ocamlformat ocaml-lsp-server earlybird

build:
	dune build

check: test

test:
	dune runtest

test-inline:
	dune runtest src

test-fast:
	make -C test fast

test-fast-basic:
	make -C test fast/basic

install:
	dune install --prefix=$(PREFIX)
	make -C $(PREFIX)/lib/tlapm/ -f Makefile.post-install

release:
	rm -rf _build/tlaps-release-dir _build/tlaps-release-version
	dune install --relocatable --prefix _build/tlaps-release-dir
	make -C _build/tlaps-release-dir/lib/tlapm -f Makefile.post-install
	cd test && env \
		USE_TLAPM=../_build/tlaps-release-dir/bin/tlapm \
		USE_LIB=../_build/tlaps-release-dir/lib/tlapm/stdlib \
		./TOOLS/do_tests fast/basic
	RELEASE_VERSION="$$(_build/tlaps-release-dir/bin/tlapm --version)" \
		&& rm -rf _build/$(RELEASE_FILE) \
		&& mv _build/tlaps-release-dir _build/$(RELEASE_NAME) \
		&& (cd _build/ && tar -czf $(RELEASE_FILE) $(RELEASE_NAME)) \
		&& rm -rf _build/$(RELEASE_NAME) \
		&& echo $$RELEASE_VERSION > _build/tlaps-release-version

release-print-version:
	@cat _build/tlaps-release-version

release-print-file:
	@RELEASE_VERSION="$$(cat _build/tlaps-release-version)" && echo $(RELEASE_FILE)

clean:
	dune clean

.PHONY: all build check test test-inline test-fast test-fast-basic install release release-print-version release-print-file clean

