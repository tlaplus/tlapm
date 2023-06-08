ZENON_SRC:=$(DUNE_SOURCEROOT)/zenon
TARGET_DIR:=$(shell pwd)

all:
	cd $(ZENON_SRC) && ./configure -coqc : -prefix "$(TARGET_DIR)"
	make -C $(ZENON_SRC) all
	make -C $(ZENON_SRC) install
	cp -vf $(TARGET_DIR)/bin/zenon ./
