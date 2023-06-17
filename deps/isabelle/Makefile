UNAME := $(shell uname)

ISABELLE_VSN:=Isabelle2011-1
ifeq ($(UNAME), Linux)
	ISABELLE_ARCHIVE:=$(ISABELLE_VSN)_bundle_x86-linux.tar.gz
endif
ifeq ($(UNAME), Darwin)
	ISABELLE_ARCHIVE:=$(ISABELLE_VSN).dmg
endif
ISABELLE_URL:=http://isabelle.in.tum.de/website-$(ISABELLE_VSN)/dist/$(ISABELLE_ARCHIVE)

ISABELLE_DIR:=Isabelle
ISABELLE_EXE:=$(shell pwd)/$(ISABELLE_DIR)/bin/isabelle
ISABELLE_OUT:=$(shell pwd)/$(ISABELLE_DIR)/heaps

# Some defaults, for the case if makefile is called not by the dune build system.
INSIDE_DUNE?=tmp
DUNE_SOURCEROOT?=../../
CACHE_DIR:=$(INSIDE_DUNE)/../../_build_cache


all: $(ISABELLE_DIR)

$(CACHE_DIR)/$(ISABELLE_ARCHIVE):
	mkdir -p $(CACHE_DIR)
	cd $(CACHE_DIR) && wget -q $(ISABELLE_URL)

$(ISABELLE_ARCHIVE): $(CACHE_DIR)/$(ISABELLE_ARCHIVE)
	rm -f $@
	ln -s $< $@

.PRECIOUS: $(ISABELLE_DIR)
$(ISABELLE_DIR): $(ISABELLE_ARCHIVE)
ifeq ($(UNAME), Linux)
	rm -rf $(ISABELLE_DIR)
	tar -xzf $<
	mv $(ISABELLE_VSN) $(ISABELLE_DIR)
endif
ifeq ($(UNAME), Darwin)
	echo $(ISABELLE_DIR)
	rm -rf $(ISABELLE_DIR)
	mkdir $(ISABELLE_DIR)
	hdiutil attach $<
	cp -R /Volumes/$(ISABELLE_VSN)/$(ISABELLE_VSN).app/Contents/Resources/$(ISABELLE_VSN)/* $(ISABELLE_DIR)
endif
	# these lines above do not work because I am lost in all these directories: 
	# ISABELLE_DIR contains .dmg and not what I expect
	cd $(ISABELLE_DIR) && rm -rf contrib/ProofGeneral* doc heaps/*/HOL lib/{classes,fonts,logo}
	cd $(ISABELLE_DIR) && cp etc/settings etc/settings.orig && echo "ISABELLE_OUTPUT=$(ISABELLE_OUT)" >> etc/settings
	cd $(ISABELLE_DIR) && cp -r $(DUNE_SOURCEROOT)/isabelle src/TLA+
	cd $(ISABELLE_DIR)/src/TLA+ && $(ISABELLE_EXE) usedir -b Pure TLA+
	cd $(ISABELLE_DIR) && rm etc/settings && mv etc/settings.orig etc/settings
ifeq ($(UNAME), Darwin)
	hdiutil umount /Volumes/$(ISABELLE_VSN)
endif

.PRECIOUS: $(ISABELLE_DIR).tar.gz
$(ISABELLE_DIR).tar.gz: $(ISABELLE_DIR)
	tar -czf $@ $<

# TODO: This is is a workaround to eliminate symlinks to directories
# 		until https://github.com/ocaml/dune/issues/7831 is resolved.
.PRECIOUS: $(ISABELLE_DIR).no-links
$(ISABELLE_DIR).no-links: $(ISABELLE_DIR)
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

.PHONY: all
