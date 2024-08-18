##
## This Makefile is called from the dune script.
## We call the Isabelle via make to avoid dune attempts to
## find a rule for building $(ISABELLE). It is already built.
##

ISABELLE_TEST=../deps/isabelle/Isabelle-test
ISABELLE=$(ISABELLE_TEST)/bin/isabelle

runtest:
	chmod -R ug+rw . $(ISABELLE_TEST)/lib/texinputs/ # Fighting the dune sandboxing...
	$(ISABELLE) build -o document=false -o browser_info=false -c -v -D .
