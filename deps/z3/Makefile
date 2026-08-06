OS_TYPE=$(patsubst CYGWIN%,Cygwin,$(shell uname))

Z3_VERS=4.15.4
Z3_URL_PREFIX=https://github.com/Z3Prover/z3/releases/download/z3-$(Z3_VERS)

ifeq ($(OS_TYPE),Linux)
    Z3_BASE_NAME=z3-${Z3_VERS}-x64-glibc-2.39
	Z3_EXEC=z3
endif
ifeq ($(OS_TYPE),Darwin)
    Z3_BASE_NAME=z3-${Z3_VERS}-x64-osx-13.7.6
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
