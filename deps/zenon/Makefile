OS_TYPE=$(patsubst CYGWIN%,Cygwin,$(shell uname))

ZENON_SRC=zenon-src

# While the values are the same in all OS types, we keep them here to state supported OS types.
ifeq ($(OS_TYPE),Linux)
	ZENON_EXEC=zenon
endif
ifeq ($(OS_TYPE),Darwin)
	ZENON_EXEC=zenon
endif
ifeq ($(OS_TYPE),Cygwin)
	ZENON_EXEC=zenon
endif

all: zenon

zenon:
	TARGET_DIR=$(shell pwd) && cd $(ZENON_SRC) && ./configure -coqc : -prefix "$${TARGET_DIR}/zenon-install"
	make -C $(ZENON_SRC) all
	make -C $(ZENON_SRC) install
	cp -vf zenon-install/bin/$(ZENON_EXEC) $@

clean:
	rm -rf zenon zenon-install
	make -C $(ZENON_SRC) clean
	rm -f $(ZENON_SRC)/config.ml

.PHONY: all clean
