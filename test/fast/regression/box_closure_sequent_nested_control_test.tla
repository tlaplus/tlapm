---- MODULE box_closure_sequent_nested_control_test ----
EXTENDS TLAPS

VARIABLE x

\* Three nested implications to FALSE are equivalent
\* to negation.
\* ~[](x = 0) is not box-closed.
\* Counterexample: x is 1 initially, then 0 forever.

THEOREM
    ASSUME ASSUME ASSUME ASSUME [](x = 0) PROVE FALSE
                         PROVE FALSE
                  PROVE FALSE
    PROVE [](~[](x = 0))
BY PTL

============================================================================
stderr: status:failed
stderr: prover:ls4
stderr: reason:false
nostderr: status:proved
nostderr: Unexpected error
nostderr: Unexpected exception
nostd*: ending abnormally
