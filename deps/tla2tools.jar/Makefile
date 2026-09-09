TLA_TOOLS_JAR_URL=https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar

# If a sibling tlaplus/ checkout in the same workspace has a locally built
# tla2tools.jar, symlink to that instead of downloading a release jar. This
# lets local SANY/TLC/etc. changes be picked up without cutting a release.
# Rebuild it with: (cd ../../../tlaplus/tlatools/org.lamport.tlatools && \
#   ant -f customBuild.xml info compile compile-test dist)
#
# Two candidate depths are tried because this Makefile runs with different
# cwds depending on how it's invoked: directly from the source tree
# (deps/tla2tools.jar/, 3 levels above the workspace root) or via dune, which
# runs rules from inside _build/default/deps/tla2tools.jar/ (5 levels above).
WORKSPACE_TLA2TOOLS_JAR := $(firstword $(wildcard \
	../../../tlaplus/tlatools/org.lamport.tlatools/dist/tla2tools.jar \
	../../../../../tlaplus/tlatools/org.lamport.tlatools/dist/tla2tools.jar))

tla2tools.jar:
ifneq ($(WORKSPACE_TLA2TOOLS_JAR),)
	ln -sf $(WORKSPACE_TLA2TOOLS_JAR) tla2tools.jar
else
	wget --progress=dot:giga $(TLA_TOOLS_JAR_URL)
endif

clean:
	rm -f tla2tools.jar

sany: tla2tools.jar

.PHONY: sany clean
