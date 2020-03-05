##########################################################
# Makefile --- Makefile for regression tests             #
#                                                        #
# Author: Damien Doligez <damien.doligez@inria.fr>       #
#                                                        #
# Copyright (C) 2008  INRIA and Microsoft Corporation    #
##########################################################

# usage:
#
# Type "make" to run the full regression test suite.
#
# If you added a foo.tla file, you can generate the corresponding
# .exact file with "make foo.exact".
#
# Type "make clean" to get rid of temporary files and test results.


.PHONY: default
default:
	./test.sh

.PHONY: quick
quick:
	./test.sh -quick

.PHONY: clean
clean:
	rm -rf temp/*
	find . -name '*.diff' -exec rm -f '{}' ';'
	find . -name 'TLA_*.thyx' -exec rm -f '{}' ';'
	find . -name 'TLA_*.thy' -exec rm -f '{}' ';'
	find . -name 'TLA_*.fp' -exec rm -f '{}' ';'
	find . -name 'TLA_*.fp.history' -exec rm -rf '{}' ';'
	find . -name '*.log' -exec rm -f '{}' ';'
