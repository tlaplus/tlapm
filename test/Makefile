# Copyright (C) 2011  INRIA and Microsoft Corporation

.PHONY: default
default: fast

.PHONY: all
all:
	./TOOLS/do_tests .

.PHONY: partial
partial:
	./TOOLS/do_tests "${SUB}"

.PHONY: fast
fast:
	./TOOLS/do_tests fast

.PHONY: medium
medium:
	./TOOLS/do_tests medium

.PHONY: slow
slow:
	./TOOLS/do_tests slow

.PHONY: stest
stest:
	./TOOLS/do_soundness_tests soundness_tests

.PHONY: junit
junit:
	./TOOLS/do_junit_tests regression_tests

.PHONY: unit
unit:
	./TOOLS/do_tests unit

.PHONY: bugs
bugs:
	./TOOLS/do_tests bugs

clean:
	find . \( \
	    -name '*.tlaps' \
	    -o -name '*.tla.out' \
	    -o -name '*.tla.err' \
	    -o -name '.tlacache' \
	    -o -name '__tlacache__' \
	    \) \
	    -prune -exec rm -rf '{}' \;
	rm -f tests.log
