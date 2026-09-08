#
# See https://isabelle.in.tum.de/dist/ for download files and their SHA256 sums.
#
OS_TYPE=$(patsubst CYGWIN%,Cygwin,$(shell uname))
HOST_CPU=$(shell uname -m)

ISABELLE_VSN=Isabelle2025

ifeq ($(OS_TYPE),Linux)
	ISABELLE_SHA256=3d1d66de371823fe31aa8ae66638f73575bac244f00b31aee1dcb62f38147c56
	ISABELLE_ARCHIVE=$(ISABELLE_VSN)_linux.tar.gz
	ISABELLE_ARCHIVE_TYPE=tgz
	ISABELLE_ARCHIVE_DIR=$(ISABELLE_VSN)
endif
ifeq ($(OS_TYPE),Darwin)
	ISABELLE_SHA256=ea5754c228857f5d9d3ae254ec9814797f2453ea290df20b2f6dcb2ef0e2e7f8
	ISABELLE_ARCHIVE=$(ISABELLE_VSN)_macos.tar.gz
	ISABELLE_ARCHIVE_TYPE=tgz
	ISABELLE_ARCHIVE_DIR=$(ISABELLE_VSN).app
endif
ifeq ($(OS_TYPE),Cygwin)
	# TODO: Fix this.
	ISABELLE_SHA256=ab449a85c0f7c483027c2000889ec93b3f7df565d9d0c6902af2d666b3b58220
	ISABELLE_ARCHIVE=$(ISABELLE_VSN)_bundle_x86-cygwin.tar.gz
	ISABELLE_ARCHIVE_TYPE=tgz
	ISABELLE_ARCHIVE_DIR=$(ISABELLE_VSN)
endif

ISABELLE_URL=https://isabelle.in.tum.de/website-$(ISABELLE_VSN)/dist/$(ISABELLE_ARCHIVE)
ISABELLE_DIR=Isabelle
ISABELLE_TEST=Isabelle-test

# Some defaults, for the case if makefile is called not by the dune build system.
PROJECT_ROOT=$(if $(DUNE_SOURCEROOT),$(DUNE_SOURCEROOT),../..)
CACHE_DIR=$(PROJECT_ROOT)/_build_cache


all: $(ISABELLE_DIR) $(ISABELLE_DIR)/src/TLA+ $(ISABELLE_TEST) Isabelle-install

# Download the isabelle archive to the cache.
$(CACHE_DIR)/$(ISABELLE_ARCHIVE):
	mkdir -p $(CACHE_DIR)
	(echo "$(ISABELLE_SHA256) *$@" | shasum -a 256 -c -) || ( \
		(rm -f $@) && \
		(wget --progress=dot:giga --directory-prefix=$(CACHE_DIR) $(ISABELLE_URL)) && \
		(echo "$(ISABELLE_SHA256) *$@" | shasum -a 256 -c -) \
	)
.PHONY: $(CACHE_DIR)/$(ISABELLE_ARCHIVE) # Have to double-check the checksum.

# Take the Isabelle archive from the cache.
$(ISABELLE_ARCHIVE): $(CACHE_DIR)/$(ISABELLE_ARCHIVE)
	rm -f $@
	ln -s $< $@

# Extract the isabelle archive and remove broken symlinks.
$(ISABELLE_DIR) $(ISABELLE_TEST): $(ISABELLE_ARCHIVE)
	rm -rf $(ISABELLE_DIR)
ifeq ($(ISABELLE_ARCHIVE_TYPE),tgz)
	tar -xzf $<
	mv $(ISABELLE_ARCHIVE_DIR) $(ISABELLE_DIR)
endif
	cd $(ISABELLE_DIR) && rm -rf ./contrib/e-3.1-1/src/lib/
	cp -r $(ISABELLE_DIR) $(ISABELLE_TEST)

# Build the TLA+ theory.
.PRECIOUS: $(ISABELLE_DIR)/src/TLA+
$(ISABELLE_DIR)/src/TLA+: $(ISABELLE_DIR)
	cd $(ISABELLE_DIR) \
		&& rm -rf contrib/ProofGeneral* doc heaps/*/HOL contrib/vscodium* contrib/vscode* \
		&& awk '/^((contrib\/(vscode_extension|vscodium))|(src\/Tools\/Demo))/{ print "#rm at TLA# " $$0; next } END { print "src/TLA+" } { print }' etc/components > etc/components.tmp \
		&& rm etc/components && mv etc/components.tmp etc/components
	mkdir -p $(ISABELLE_DIR)/src/TLA+ \
		&& cp -a ../../isabelle/* $(ISABELLE_DIR)/src/TLA+/ \
		&& chmod -R u+w $(ISABELLE_DIR)/src/TLA+/ \
		&& make -C $(ISABELLE_DIR)/src/TLA+/ clean
	cd $(ISABELLE_DIR)/ \
		&& ./bin/isabelle build -o system_heaps -o document=false -b -v -d src/Pure Pure \
		&& ./bin/isabelle build -o system_heaps -o document=false -b -c -v -d src/TLA+ TLA+ \
		&& rm -rf ./heaps/polyml-*/log/*

# Bake the options "isabelle process -l TLA+" would otherwise reload via the
# JVM on every invocation into a small extra heap layer on top of TLA+, so
# Params.isabelle (src/params.ml) can just load that layer instead.
$(ISABELLE_DIR)/etc/ml_platform.txt: $(ISABELLE_DIR)/src/TLA+
	cd $(ISABELLE_DIR) \
		&& ./bin/isabelle env sh -c 'basename "$$ML_HOME"' > etc/ml_platform.txt
	cd $(ISABELLE_DIR) \
		&& PLATFORM=$$(cat etc/ml_platform.txt) \
		&& ./bin/isabelle process \
			-e 'ML_Heap.save_child "heaps/polyml-5.9.1_'"$$PLATFORM"'/Options";' \
			-d src/TLA+ -l TLA+

# Assemble the minimal subset of the built distribution that tlapm actually
# needs at runtime.
Isabelle-install: $(ISABELLE_DIR)/etc/ml_platform.txt
	rm -rf $@
	mkdir -p $@/poly $@/etc $@/heaps
	cp -a $(ISABELLE_DIR)/etc/ISABELLE_IDENTIFIER $@/etc/ISABELLE_IDENTIFIER
	PLATFORM=$$(cat $(ISABELLE_DIR)/etc/ml_platform.txt) \
		&& cp -a $(ISABELLE_DIR)/contrib/polyml-5.9.1/$$PLATFORM/. $@/poly/ \
		&& cp -a $(ISABELLE_DIR)/heaps/polyml-5.9.1_$$PLATFORM/Pure $@/heaps/Pure \
		&& cp -a $(ISABELLE_DIR)/heaps/polyml-5.9.1_$$PLATFORM/TLA+ $@/heaps/TLA+ \
		&& cp -a $(ISABELLE_DIR)/heaps/polyml-5.9.1_$$PLATFORM/Options $@/heaps/Options

clean:
	rm -rf $(ISABELLE_ARCHIVE) $(ISABELLE_DIR) $(ISABELLE_TEST) Isabelle-install

.PHONY: all clean
