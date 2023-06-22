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
RELEASE_VERSION=$(shell ./src/tlapm.exe  --version)
RELEASE_NAME=tlaps-$(RELEASE_VERSION)-$(HOST_CPU)-$(HOST_OS)
RELEASE_FILE=$(RELEASE_NAME).tar.gz

PREFIX=$(OPAM_SWITCH_PREFIX)

all: build

opam-deps:
	opam install ./ --deps-only

build:
	dune build
	if [ -z "`grep 'Makefile.post-install' tlapm.opam`" ] ; then \
	 	sed -i '/"dune" "install"/a \ \ ["%{make}%" "-C" "%{lib}%/tlapm" "-f" "Makefile.post-install"]' tlapm.opam; \
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
	rm -rf $(RELEASE_NAME) $(RELEASE_FILE)
	dune install --relocatable --prefix $(RELEASE_NAME)
	make -C $(RELEASE_NAME)/lib/tlapm -f Makefile.post-install
	tar -czf $(RELEASE_FILE) $(RELEASE_NAME)
	rm -rf $(RELEASE_NAME)

release-print-file:
	@echo $(RELEASE_FILE)

clean:
	dune clean

.PHONY: all build check test test-inline test-fast test-fast-basic install release release-print-file clean

