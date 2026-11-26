---- MODULE box_closure_sequent_diamond_control_test ----
EXTENDS TLAPS

VARIABLE x

\* The inner sequent is ~<>(x = 0).
\* It is box-closed but not diamond-closed.
\* The enclosing sequent is equivalent to <>(x = 0).
\* Counterexample: x is 0 initially, then 1 forever.

THEOREM
    ASSUME ASSUME ASSUME <>(x = 0) PROVE FALSE
                  PROVE FALSE
    PROVE [](<>(x = 0))
BY PTL

============================================================================
stderr: status:failed
stderr: prover:ls4
stderr: reason:false
nostderr: status:proved
nostderr: Unexpected error
nostderr: Unexpected exception
nostd*: ending abnormally
