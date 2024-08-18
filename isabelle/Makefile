ISABELLE=isabelle

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

# Launch Isabelle / Jedit to edit the theory, examples, tests.
jedit:
	$(ISABELLE) jedit -d . Constant.thy

clean:
	rm -rf output/ examples/output/
