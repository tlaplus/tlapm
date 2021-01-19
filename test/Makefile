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

.PHONY: smt
smt:
	./TOOLS/do_tests smt_tests

clean:
	find . \( -name '*.tlaps' -o -name '*.tla.out' -o -name '*.tla.err' \) \
             -prune -exec rm -rf '{}' \;
	rm -f tests.log
