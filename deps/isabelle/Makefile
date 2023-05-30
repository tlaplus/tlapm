ISABELLE_VSN:=Isabelle2011-1
ISABELLE_TGZ:=$(ISABELLE_VSN)_bundle_x86-linux.tar.gz
ISABELLE_URL:=http://isabelle.in.tum.de/website-$(ISABELLE_VSN)/dist/$(ISABELLE_TGZ)
ISABELLE_DIR:=Isabelle
ISABELLE_EXE:=$(shell pwd)/$(ISABELLE_DIR)/bin/isabelle
ISABELLE_OUT:=$(shell pwd)/$(ISABELLE_DIR)/heaps

all: $(ISABELLE_DIR)

$(ISABELLE_TGZ):
	wget -q $(ISABELLE_URL)

.PRECIOUS: $(ISABELLE_DIR).sexp
$(ISABELLE_DIR).sexp: $(ISABELLE_TGZ)
	rm -rf $(ISABELLE_DIR) $(ISABELLE_DIR).sexp
	tar -xzf $<
	mv $(ISABELLE_VSN) $(ISABELLE_DIR)
	cd $(ISABELLE_DIR) && rm -rf contrib/ProofGeneral* doc heaps/*/HOL lib/{classes,fonts,logo}
	cd $(ISABELLE_DIR) && echo "ISABELLE_OUTPUT=$(ISABELLE_OUT)" >> etc/settings
	cd $(ISABELLE_DIR) && cp -r $(DUNE_SOURCEROOT)/isabelle src/TLA+
	cd $(ISABELLE_DIR)/src/TLA+ && $(ISABELLE_EXE) usedir -b Pure TLA+
	(echo "(" && (find $(ISABELLE_DIR) -type f) && echo ")") > $(ISABELLE_DIR).sexp

.PHONY: all
