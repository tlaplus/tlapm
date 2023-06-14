RELEASE_NAME:=tlaps-$(shell git describe --tags)-$(shell uname -m)-$(shell uname -s | tr '[:upper:]' '[:lower:]')

PREFIX?=$(OPAM_SWITCH_PREFIX)

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

install:
	dune install --prefix=$(PREFIX)
	make -C $(PREFIX)/lib/tlapm/ -f Makefile.post-install

release:
	rm -rf $(RELEASE_NAME) $(RELEASE_NAME).tar.gz
	dune install --relocatable --prefix $(RELEASE_NAME)
	make -C $(RELEASE_NAME)/lib/tlapm -f Makefile.post-install
	tar -czf $(RELEASE_NAME).tar.gz $(RELEASE_NAME)
	rm -rf $(RELEASE_NAME)

clean:
	dune clean

.PHONY: all build check test install release clean

