OS_TYPE=$(patsubst CYGWIN%,Cygwin,$(shell uname))
HOST_CPU=$(shell uname -m)

ISABELLE_VSN=Isabelle2024

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
ISABELLE_TEST=Isabelle-test

# Some defaults, for the case if makefile is called not by the dune build system.
PROJECT_ROOT=$(if $(DUNE_SOURCEROOT),$(DUNE_SOURCEROOT),../..)
CACHE_DIR=$(PROJECT_ROOT)/_build_cache


all: $(ISABELLE_DIR) $(ISABELLE_DIR)/src/TLA+ $(ISABELLE_TEST) Isabelle.exec-files

# Download the isabelle archive to the cache.
$(CACHE_DIR)/$(ISABELLE_ARCHIVE):
	mkdir -p $(CACHE_DIR)
	cd $(CACHE_DIR) && wget -nv $(ISABELLE_URL)

# Take the Isabelle archive from the cache.
$(ISABELLE_ARCHIVE): $(CACHE_DIR)/$(ISABELLE_ARCHIVE)
	rm -f $@
	ln -s $< $@

# Extract the isabelle archive and remove the symlinks.
# TODO: This is is a workaround to eliminate symlinks to directories
# 		until https://github.com/ocaml/dune/issues/7831 is resolved.
$(ISABELLE_DIR) $(ISABELLE_TEST): $(ISABELLE_ARCHIVE)
	rm -rf $(ISABELLE_DIR)
ifeq ($(ISABELLE_ARCHIVE_TYPE),tgz)
	tar -xzf $<
	mv $(ISABELLE_ARCHIVE_DIR) $(ISABELLE_DIR)
endif
	cd $(ISABELLE_DIR) && rm -rf ./contrib/e-3.0.03-1/src/lib/
ifeq ($(OS_TYPE),Darwin)
	cd $(ISABELLE_DIR) && cd contrib/jdk-21.0.3/arm64-darwin/ \
		&& (find . -type link | xargs rm) \
		&& mv zulu-21.jdk/Contents/Home/* ./
	cd $(ISABELLE_DIR) && cd contrib/jdk-21.0.3/x86_64-darwin/ \
		&& (find . -type link | xargs rm) \
		&& mv zulu-21.jdk/Contents/Home/* ./
endif
	cp -r $(ISABELLE_DIR) $(ISABELLE_TEST)

# Build the TLA+ theory.
.PRECIOUS: $(ISABELLE_DIR)/src/TLA+
$(ISABELLE_DIR)/src/TLA+: $(ISABELLE_DIR)
	cd $(ISABELLE_DIR) \
		&& rm -rf contrib/ProofGeneral* doc heaps/*/HOL contrib/vscodium* contrib/vscode* \
		&& sed -i -e 's@^\(contrib/vscode_extension\|contrib/vscodium\|src/Tools/Demo\)@#rm at TLA# \1@' etc/components \
		&& echo 'src/TLA+' >> etc/components
	cd $(ISABELLE_DIR) \
		&& HEAPS_PATH=$(shell pwd)/$(ISABELLE_DIR)/heaps \
		&& if [ "$(HOST_CPU)" = "x86_64" ] ; then sed -i -e 's/^ML_PLATFORM=.*$$/ML_PLATFORM="$${ISABELLE_PLATFORM64:-$$ISABELLE_PLATFORM}"/' etc/settings ; fi \
		&& cp etc/settings etc/settings.target \
		&& echo "ISABELLE_OUTPUT=$$HEAPS_PATH" >> etc/settings
	mkdir -p $(ISABELLE_DIR)/src/TLA+ \
		&& cp -a ../../isabelle/* $(ISABELLE_DIR)/src/TLA+/ \
		&& chmod -R u+w $(ISABELLE_DIR)/src/TLA+/ \
		&& make -C $(ISABELLE_DIR)/src/TLA+/ clean
	cd $(ISABELLE_DIR)/ \
		&& ./bin/isabelle build -o system_heaps -o document=false -b -v -d src/Pure Pure \
		&& ./bin/isabelle build -o system_heaps -o document=false -b -c -v -d src/TLA+ TLA+ \
		&& rm -rf ./heaps/polyml-*/log/*
	cd $(ISABELLE_DIR) \
		&& rm etc/settings \
		&& mv etc/settings.target etc/settings

# TODO: This is a workaround, because the dune install removes all the executable
# 		flags (or sets on all the files). Here we generate a script to restore the flags.
Isabelle.exec-files: $(ISABELLE_DIR)
	echo "$(shell find $(ISABELLE_DIR) -type f $(FIND_EXEC))" > $@

clean:
	rm -rf $(ISABELLE_ARCHIVE) $(ISABELLE_DIR) $(ISABELLE_TEST) Isabelle.exec-files

.PHONY: all clean
