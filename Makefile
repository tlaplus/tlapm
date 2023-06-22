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

opam-deps:
	opam install ./ --deps-only --yes --working-dir

build:
	dune build
	if [ -z "`grep 'Makefile.post-install' tlapm.opam`" ] ; then \
		rm -f tlapm.opam.tmp && \
		mv tlapm.opam tlapm.opam.tmp && \
		cat tlapm.opam.tmp | awk '/"dune" "install"/{print; print "  [\"%{make}%\" \"-C\" \"%{lib}%/tlapm\" \"-f\" \"Makefile.post-install\"]" ; next} //{print}' > tlapm.opam && \
		rm -f tlapm.opam.tmp ; \
	fi

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
	rm -rf _build/tlaps-release-dir
	dune install --relocatable --prefix _build/tlaps-release-dir
	RELEASE_VERSION="$$(_build/tlaps-release-dir/bin/tlapm --version)" \
		&& rm -rf _build/$(RELEASE_FILE) \
		&& make -C _build/tlaps-release-dir/lib/tlapm -f Makefile.post-install \
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

