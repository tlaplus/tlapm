OS_TYPE=$(patsubst CYGWIN%,Cygwin,$(shell uname))
HOST_CPU=$(shell uname -m)

ISABELLE_VSN=Isabelle2011-1

ifeq ($(OS_TYPE),Linux)
	ISABELLE_ARCHIVE=$(ISABELLE_VSN)_bundle_x86-linux.tar.gz
	ISABELLE_ARCHIVE_TYPE=tgz
endif
ifeq ($(OS_TYPE),Darwin)
	ISABELLE_ARCHIVE=$(ISABELLE_VSN).dmg
	ISABELLE_ARCHIVE_TYPE=dmg
endif
ifeq ($(OS_TYPE),Cygwin)
	ISABELLE_ARCHIVE=$(ISABELLE_VSN)_bundle_x86-cygwin.tar.gz
	ISABELLE_ARCHIVE_TYPE=tgz
endif

ISABELLE_URL=http://isabelle.in.tum.de/website-$(ISABELLE_VSN)/dist/$(ISABELLE_ARCHIVE)
ISABELLE_DIR=Isabelle

# Some defaults, for the case if makefile is called not by the dune build system.
PROJECT_ROOT=../..
CACHE_DIR=$(PROJECT_ROOT)/_build_cache


all: $(ISABELLE_DIR) $(ISABELLE_DIR)/src/TLA+ $(ISABELLE_DIR).no-links Isabelle.post-install

# Download the isabelle archive to the cache.
$(CACHE_DIR)/$(ISABELLE_ARCHIVE):
	mkdir -p $(CACHE_DIR)
	cd $(CACHE_DIR) && wget -q $(ISABELLE_URL)

# Take the Isabelle archive from the cache.
$(ISABELLE_ARCHIVE): $(CACHE_DIR)/$(ISABELLE_ARCHIVE)
	rm -f $@
	ln -s $< $@

# Extract the isabelle archive.
$(ISABELLE_DIR): $(ISABELLE_ARCHIVE)
ifeq ($(ISABELLE_ARCHIVE_TYPE),tgz)
	rm -rf $(ISABELLE_DIR)
	tar -xzf $<
	mv $(ISABELLE_VSN) $(ISABELLE_DIR)
endif
ifeq ($(ISABELLE_ARCHIVE_TYPE),dmg)
	rm -rf isabelle-dmg
	hdiutil attach "$<" -quiet -readonly -nobrowse -mountpoint "$(shell pwd)/isabelle-dmg"
	cp -a "isabelle-dmg/$(ISABELLE_VSN).app/Contents/Resources/$(ISABELLE_VSN)" "$@"
	hdiutil detach "$(shell pwd)/isabelle-dmg" -quiet
	rm -rf isabelle-dmg
endif

# Build the TLA+ theory.
.PRECIOUS: $(ISABELLE_DIR)/src/TLA+
$(ISABELLE_DIR)/src/TLA+: $(ISABELLE_DIR)
	cd $(ISABELLE_DIR) \
		&& rm -rf contrib/ProofGeneral* doc heaps/*/HOL lib/{classes,fonts,logo}
	cd $(ISABELLE_DIR) \
		&& HEAPS_PATH=$(shell pwd)/$(ISABELLE_DIR)/heaps \
		&& if [ "$(HOST_CPU)" = "x86_64" ] ; then sed -i 's/^ML_PLATFORM=.*$$/ML_PLATFORM="$${ISABELLE_PLATFORM64:-$$ISABELLE_PLATFORM}"/' etc/settings ; fi \
		&& cp etc/settings etc/settings.target \
		&& echo "ISABELLE_OUTPUT=$$HEAPS_PATH" >> etc/settings
	mkdir -p $(ISABELLE_DIR)/src/TLA+ \
		&& cp -a theories/TLA+/* $(ISABELLE_DIR)/src/TLA+/
	cd $(ISABELLE_DIR)/src/Pure \
		&& ../../bin/isabelle make
	cd $(ISABELLE_DIR)/src/TLA+ \
		&& ../../bin/isabelle usedir -b Pure TLA+
	cd $(ISABELLE_DIR) \
		&& rm etc/settings \
		&& mv etc/settings.target etc/settings

# TODO: This is is a workaround to eliminate symlinks to directories
# 		until https://github.com/ocaml/dune/issues/7831 is resolved.
.PRECIOUS: $(ISABELLE_DIR).no-links
$(ISABELLE_DIR).no-links: $(ISABELLE_DIR) $(ISABELLE_DIR)/src/TLA+
	rm -rf $@
	cd $< && rm ./contrib/jre1.6.0_27_x86-linux/jre1.6.0_27/man/ja
	cd $< && rm ./contrib/polyml-5.4.0/src
	cd $< && rm ./contrib/polyml && mv ./contrib/polyml-5.4.0 ./contrib/polyml
	touch $@

# TODO: This is a workaround, because the dune install removes all the executable
# 		flags (or sets on all the files). Here we generate a script to restore the flags.
Isabelle.post-install: $(ISABELLE_DIR).no-links
	echo "FILES=$(shell find $(ISABELLE_DIR) -type f -executable)" > $@
	echo "all:\n\t chmod +x \$$(FILES)" >> $@

clean:
	rm -rf $(ISABELLE_ARCHIVE) $(ISABELLE_DIR) $(ISABELLE_DIR).no-links Isabelle.post-install

.PHONY: all clean
