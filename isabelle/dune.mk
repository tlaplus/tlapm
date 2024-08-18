##
## This Makefile is called from the dune script.
## We call the Isabelle via make to avoid dune attempts to
## find a rule for building $(ISABELLE). It is already built.
##

ISABELLE=../deps/isabelle/Isabelle-test/bin/isabelle

runtest:
	$(ISABELLE) build -o document=false -o browser_info=false -c -v -D .
