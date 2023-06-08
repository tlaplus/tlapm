Z3_VERS=4.8.9
Z3_URL_PREFIX=https://github.com/Z3Prover/z3/releases/download/z3-$(Z3_VERS)
Z3_BASE_NAME=z3-${Z3_VERS}-x64-ubuntu-16.04

all: z3

$(Z3_BASE_NAME).zip:
	wget $(Z3_URL_PREFIX)/$@

$(Z3_BASE_NAME): $(Z3_BASE_NAME).zip
	rm -rf $@
	unzip $<

z3: $(Z3_BASE_NAME)
	cp -f $</bin/z3 ./

clean:
	rm -rf z3 $(Z3_BASE_NAME) $(Z3_BASE_NAME).zip

.PHONY: all clean
