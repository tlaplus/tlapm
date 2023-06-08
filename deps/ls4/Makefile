LS4_VERS=1.0
LS4_URL_PREFIX=https://github.com/quickbeam123/ls4/archive
LS4_BASE_NAME=ls4-$(LS4_VERS)

all: ls4

v$(LS4_VERS).zip:
	wget $(LS4_URL_PREFIX)/$@

$(LS4_BASE_NAME): v$(LS4_VERS).zip
	rm -rf $@
	unzip $<
	touch $@ # To avoid rebuilds.
	( set -x && patch -p0 <ls4.patch )
	cd $(LS4_BASE_NAME)/core && cc -c aiger.c
	make -C $(LS4_BASE_NAME)/core

ls4: $(LS4_BASE_NAME)
	cp -f $</core/ls4 ./

clean:
	rm -rf ls4 $(LS4_BASE_NAME) v$(LS4_VERS).zip

.PHONY: all clean
