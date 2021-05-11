All files ending in `_test.tla` in this subdirectory are unit tests for the SMT-LIB encoding of TLA+1 proof obligations. There are to be executed by `tlapm` with the option `--method smt`.

- `basic` contains very basic tests that merely check if a feature is present;
- `advanced` contains more advanced problems;
- `bools` contains tests about the ambiguity of terms and formulas;
- `epsilon` contains tests about the `CHOOSE` operator;
- `lang` contains tests that check if a language feature of TLA+1 is supported;
- `lang2` contains tests that check if a language feature of TLA+2 is supported
