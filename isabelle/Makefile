.PHONY: rebuild heap-only

# Generate theory information (in HTML and PDF formats) as well as the main
# heap file for the TLA+ object logic. By default these will be generated
# in the (hidden) directory ~/.isabelle/ (in heaps/ for the heap and in
# browser_info/ for the documentation). The default path can be changed in
# file etc/settings beneath the Isabelle home (i.e., where the Isabelle
# distribution is installed).
rebuild:
	isabelle usedir -b -i true -d pdf Pure TLA+

heap-only:
	isabelle build -v -d . -b TLA+
