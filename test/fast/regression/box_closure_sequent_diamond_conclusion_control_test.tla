---- MODULE box_closure_sequent_diamond_conclusion_control_test ----
EXTENDS TLAPS

VARIABLES x, y

\* The inner sequent is [](x = 0) => [](y = 0).
\* It is not diamond-closed.
\* Its negation is therefore not box-closed.
\* Counterexample: x is always 0;
\* y is initially 1, then 0 forever.

THEOREM
    ASSUME ASSUME ASSUME [](x = 0) PROVE [](y = 0)
                  PROVE FALSE
    PROVE [](~([](x = 0) => [](y = 0)))
BY PTL

============================================================================
stderr: status:failed
stderr: prover:ls4
stderr: reason:false
nostderr: status:proved
nostderr: Unexpected error
nostderr: Unexpected exception
nostd*: ending abnormally
