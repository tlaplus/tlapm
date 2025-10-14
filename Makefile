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

PREFIX=$(OPAM_SWITCH_PREFIX)

DUNE_BUILD_DIR=_build

all: build

opam-update: # Update the package lists and install updates.
	opam update
	opam upgrade

opam-deps:
	opam install ./ --deps-only --with-test --yes --working-dir

opam-deps-opt:
	opam install --yes eio_main lsp

opam-deps-dev:
	opam install --yes ocamlformat ocaml-lsp-server earlybird

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

fmt:
	# Only the LSP part is not formatted automatically.
	cd lsp && dune fmt

install:
	dune install --prefix=$(PREFIX)
	make -C $(PREFIX)/lib/tlapm/ -f Makefile.post-install

TLAPM_RELEASE_DIR_NAME=tlapm
TLAPM_RELEASE_DIR=$(DUNE_BUILD_DIR)/$(TLAPM_RELEASE_DIR_NAME)
$(TLAPM_RELEASE_DIR): build
#	rm -rf $(TLAPM_RELEASE_DIR)
	dune install --relocatable --prefix $(TLAPM_RELEASE_DIR)
	make -C $(TLAPM_RELEASE_DIR)/lib/tlapm -f Makefile.post-install
	cd test && env \
		USE_TLAPM=../$(TLAPM_RELEASE_DIR)/bin/tlapm \
		USE_LIB=../$(TLAPM_RELEASE_DIR)/lib/tlapm/stdlib \
		./TOOLS/do_tests fast/basic

$(TLAPM_RELEASE_DIR).tar.gz: $(TLAPM_RELEASE_DIR)
	cd $(DUNE_BUILD_DIR) && tar -czf $(TLAPM_RELEASE_DIR_NAME).tar.gz $(TLAPM_RELEASE_DIR_NAME)

# Use RELEASE_VERSION from Make CLI args; if not present, use TLAPM build version
# Override variable like "make release RELEASE_VERSION=1.6.0"
TLAPM_VERSION_FILE = $(DUNE_BUILD_DIR)/tlapm-release-version
$(TLAPM_VERSION_FILE): $(TLAPM_RELEASE_DIR)
	if [ -z "$(RELEASE_VERSION)" ]; then \
		RELEASE_VERSION=$$($(TLAPM_RELEASE_DIR)/bin/tlapm --version); \
	fi; \
	echo $${RELEASE_VERSION} > $(TLAPM_VERSION_FILE)

release: $(TLAPM_RELEASE_DIR).tar.gz $(TLAPM_VERSION_FILE)
	TLAPM_RELEASE_VERSION="$$(cat $(TLAPM_VERSION_FILE))"; \
	TLAPM_RELEASE_NAME=tlapm-$${TLAPM_RELEASE_VERSION}-$(HOST_CPU)-$(HOST_OS); \
	mv $(TLAPM_RELEASE_DIR).tar.gz $(DUNE_BUILD_DIR)/$${TLAPM_RELEASE_NAME}.tar.gz;

release-print-version: $(TLAPM_VERSION_FILE)
	RELEASE_VERSION="$$(cat $(TLAPM_VERSION_FILE))"; \
	echo $${RELEASE_VERSION}

release-print-file: $(TLAPM_VERSION_FILE)
	cat $(TLAPM_VERSION_FILE)

clean:
	dune clean

.PHONY: all build check test test-inline test-fast test-fast-basic install $(TLAPM_VERSION_FILE) release release-print-version release-print-file clean

