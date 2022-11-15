Like the unit/ directory, this directory is for unit tests (one PO per test), but it is for negative tests.  A test succeeds if the test script returns the message 'FAILED'

(Note: Currently it does not seem possible to change the test script so that a test succeeds if the provers fail to prove something.  In the case of SMT solvers, the intented output for these unit tests is SAT, because the theorems are effectively unprovable.)
