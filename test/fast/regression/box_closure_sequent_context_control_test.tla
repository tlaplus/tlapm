---- MODULE box_closure_sequent_context_control_test ----
EXTENDS TLAPS

VARIABLE x

\* c and d are rigid, but x is flexible.
\* The last assumption is not diamond-closed.
\* The quantified sequent is equivalent to x # 0.
\* Counterexample: x is 1 initially, then 0 forever.

THEOREM
    ASSUME ASSUME NEW c,
                  c = 0,
                  NEW d,
                  d = c /\ x = 0
           PROVE FALSE
    PROVE [](\A c : c = 0 =>
                (\A d : (d = c /\ x = 0) => FALSE))
BY PTL

============================================================================
stderr: status:failed
stderr: prover:ls4
stderr: reason:false
nostderr: status:proved
nostderr: Unexpected error
nostderr: Unexpected exception
nostd*: ending abnormally
