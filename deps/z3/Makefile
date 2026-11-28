OS_TYPE=$(patsubst CYGWIN%,Cygwin,$(shell uname))
HOST_CPU=$(shell uname -m)

Z3_VERS=5.4.1
Z3_URL_PREFIX=https://github.com/Z3Prover/z3/releases/download/z3-$(Z3_VERS)

ifeq ($(OS_TYPE),Linux)
    Z3_BASE_NAME=z3-${Z3_VERS}-x64-glibc-2.39
	Z3_EXEC=z3
endif
ifeq ($(OS_TYPE),Darwin)
ifeq ($(HOST_CPU),arm64)
    Z3_BASE_NAME=z3-${Z3_VERS}-arm64-osx-13.3
else
    Z3_BASE_NAME=z3-${Z3_VERS}-x64-osx-13.3
endif
	Z3_EXEC=z3
endif
ifeq ($(OS_TYPE),Cygwin)
    Z3_BASE_NAME=z3-${Z3_VERS}-x86-win
	Z3_EXEC=z3.exe
endif

all: z3

$(Z3_BASE_NAME).zip:
	wget --progress=dot:giga $(Z3_URL_PREFIX)/$@

$(Z3_BASE_NAME): $(Z3_BASE_NAME).zip
	rm -rf $@
	unzip $<

z3: $(Z3_BASE_NAME)
	cp -f $</bin/$(Z3_EXEC) $@
	chmod ugo+x $@

clean:
	rm -rf z3 $(Z3_BASE_NAME) $(Z3_BASE_NAME).zip

.PHONY: all clean
