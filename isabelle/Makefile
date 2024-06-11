.PHONY: rebuild heap-only clean

# Generate theory information (in HTML and PDF formats) as well as the main
# heap file for the TLA+ object logic. By default these will be generated
# in the (hidden) directory ~/.isabelle/ (in heaps/ for the heap and in
# browser_info/ for the documentation). The default path can be changed in
# file etc/settings beneath the Isabelle home (i.e., where the Isabelle
# distribution is installed).
rebuild:
	isabelle build -o document -o browser_info -b -c -v -D .

heap-only:
	isabelle build -o document=false -o browser_info=false -b -c -v -D .

clean:
	rm -rf output/
