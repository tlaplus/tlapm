OS_TYPE=$(patsubst CYGWIN%,Cygwin,$(shell uname))
HOST_CPU=$(shell uname -m)

ISABELLE_VSN=Isabelle2024-RC3

ifeq ($(OS_TYPE),Linux)
	ISABELLE_ARCHIVE=$(ISABELLE_VSN)_linux.tar.gz
	ISABELLE_ARCHIVE_TYPE=tgz
	ISABELLE_ARCHIVE_DIR=$(ISABELLE_VSN)
	FIND_EXEC=-executable
endif
ifeq ($(OS_TYPE),Darwin)
	ISABELLE_ARCHIVE=$(ISABELLE_VSN)_macos.tar.gz
	ISABELLE_ARCHIVE_TYPE=tgz
	ISABELLE_ARCHIVE_DIR=$(ISABELLE_VSN).app
	FIND_EXEC=-perm +111
endif
ifeq ($(OS_TYPE),Cygwin)
	# TODO: Fix this.
	ISABELLE_ARCHIVE=$(ISABELLE_VSN)_bundle_x86-cygwin.tar.gz
	ISABELLE_ARCHIVE_TYPE=tgz
	ISABELLE_ARCHIVE_DIR=$(ISABELLE_VSN)
	FIND_EXEC=-executable
endif

ISABELLE_URL=https://isabelle.in.tum.de/website-$(ISABELLE_VSN)/dist/$(ISABELLE_ARCHIVE)
ISABELLE_DIR=Isabelle

# Some defaults, for the case if makefile is called not by the dune build system.
PROJECT_ROOT=../..
CACHE_DIR=$(PROJECT_ROOT)/_build_cache


all: $(ISABELLE_DIR) $(ISABELLE_DIR)/src/TLA+ $(ISABELLE_DIR).no-links Isabelle.exec-files

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
	mv $(ISABELLE_ARCHIVE_DIR) $(ISABELLE_DIR)
endif

# Build the TLA+ theory.
.PRECIOUS: $(ISABELLE_DIR)/src/TLA+
$(ISABELLE_DIR)/src/TLA+: $(ISABELLE_DIR)
	cd $(ISABELLE_DIR) \
		&& rm -rf contrib/ProofGeneral* doc heaps/*/HOL
	cd $(ISABELLE_DIR) \
		&& HEAPS_PATH=$(shell pwd)/$(ISABELLE_DIR)/heaps \
		&& if [ "$(HOST_CPU)" = "x86_64" ] ; then sed -i -e 's/^ML_PLATFORM=.*$$/ML_PLATFORM="$${ISABELLE_PLATFORM64:-$$ISABELLE_PLATFORM}"/' etc/settings ; fi \
		&& cp etc/settings etc/settings.target \
		&& echo "ISABELLE_OUTPUT=$$HEAPS_PATH" >> etc/settings
	mkdir -p $(ISABELLE_DIR)/src/TLA+ \
		&& cp -a theories/TLA+/* $(ISABELLE_DIR)/src/TLA+/ \
		&& chmod -R u+w $(ISABELLE_DIR)/src/TLA+/
	cd $(ISABELLE_DIR)/ \
		&& ./bin/isabelle build -o system_heaps -o document=false -b -v -d src/Pure Pure \
		&& ./bin/isabelle build -o system_heaps -o document=false -b -c -v -d src/TLA+ TLA+
	cd $(ISABELLE_DIR) \
		&& rm etc/settings \
		&& mv etc/settings.target etc/settings

# TODO: This is is a workaround to eliminate symlinks to directories
# 		until https://github.com/ocaml/dune/issues/7831 is resolved.
.PRECIOUS: $(ISABELLE_DIR).no-links
$(ISABELLE_DIR).no-links: $(ISABELLE_DIR) $(ISABELLE_DIR)/src/TLA+
	rm -rf $@
	cd $< && rm -rf ./contrib/e-3.0.03-1/src/lib/
ifeq ($(OS_TYPE),Darwin)
	cd $< && cd contrib/jdk-21.0.3/arm64-darwin/ \
		&& (find . -type link | xargs rm) \
		&& mv zulu-21.jdk/Contents/Home/* ./
	cd $< && cd contrib/jdk-21.0.3/x86_64-darwin/ \
		&& (find . -type link | xargs rm) \
		&& mv zulu-21.jdk/Contents/Home/* ./
	cd $< && rm -rf contrib/vscodium-1.70.1
endif
	touch $@

# TODO: This is a workaround, because the dune install removes all the executable
# 		flags (or sets on all the files). Here we generate a script to restore the flags.
Isabelle.exec-files: $(ISABELLE_DIR).no-links
	echo "$(shell find $(ISABELLE_DIR) -type f $(FIND_EXEC))" > $@

clean:
	rm -rf $(ISABELLE_ARCHIVE) $(ISABELLE_DIR) $(ISABELLE_DIR).no-links Isabelle.exec-files

.PHONY: all clean
