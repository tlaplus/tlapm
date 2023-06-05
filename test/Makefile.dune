#
# See test logs in ../_build/default/test/tests.log
#
TEST_DIRS=$(shell find . -type d | grep -v 'TOOLS')
TEST_FILES=$(shell find . -name '*.tla')

all:
	dune runtest -f

$(TEST_DIRS) $(TEST_FILES):
	env TEST_CASE=$@ dune runtest -f

.PHONY: all $(TEST_DIRS) $(TEST_FILES)
