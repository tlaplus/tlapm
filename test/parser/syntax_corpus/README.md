This is a corpus of TLA⁺ syntax inputs along with their expected parse tree outputs.
The tests are only intended to exercise syntax parsing and are often invalid at the semantic level (referencing nonexistent variable names, for example).
The tests use the format developed by tree-sitter, which you can see [here](https://tree-sitter.github.io/tree-sitter/creating-parsers#command-test).
Syntax inputs which are intended to cause a parse failure are tagged with `:error` in the test case header.
Every TLA⁺ tool that parses the language should adapt this corpus to ensure parser conformance.
Currently, there are three existing tools that implement a TLA⁺ parser:
1. [SANY](https://github.com/tlaplus/tlaplus/tree/master/tlatools/org.lamport.tlatools/src/tla2sany), which has adapted these tests
2. [TLAPM](https://github.com/tlaplus/tlapm), which has not yet adapted these tests
3. [tree-sitter-tlaplus](https://github.com/tlaplus-community/tree-sitter-tlaplus), which has adapted these tests

Translating a given tool's internal parse tree format to match the standardized format used by these tests is a lot of work, but ensures very thorough testing of the parser and exposes the ability to rapidly add regression tests to all parsers if a tricky parsing bug is uncovered in one of the tools.
