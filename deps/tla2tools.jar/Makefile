TLA_TOOLS_JAR_URL=https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
	
tla2tools.jar:
	wget --progress=dot:giga $(TLA_TOOLS_JAR_URL)

clean:
	rm tla2sany.jar

sany: tla2tools.jar

.PHONY: sany clean
