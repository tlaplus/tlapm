ISABELLE=isabelle
SRC_ROOT=$(if $(DUNE_SOURCEROOT),$(DUNE_SOURCEROOT),..)

.PHONY: rebuild heap-only dune-runtest clean

# Generate theory information (in HTML and PDF formats) as well as the main
# heap file for the TLA+ object logic. By default these will be generated
# in the (hidden) directory ~/.isabelle/ (in heaps/ for the heap and in
# browser_info/ for the documentation). The default path can be changed in
# file etc/settings beneath the Isabelle home (i.e., where the Isabelle
# distribution is installed).
rebuild:
	$(ISABELLE) build -o document -o browser_info -b -c -v -D .

heap-only:
	$(ISABELLE) build -o document=false -o browser_info=false -b -c -v -D .

# This is invoked from the dune file to run the tests.
# The tex files might be readonly in the sandbox and Isabelle copies
# them several times, and thus fails by overwriting a readonly file.
dune-runtest:
	chmod 644 examples/document/root.tex document/root.tex
	$(SRC_ROOT)/deps/isabelle/Isabelle/bin/isabelle build -o document=false -o browser_info=false -c -v -D .

clean:
	rm -rf output/ examples/output/
