-------------- MODULE box_closure_sequent_state_conclusion_control_test --------------

\* The implication holds initially and fails once y becomes 1 while x stays 0.

EXTENDS TLAPS

VARIABLES x, y

THEOREM ASSUME ASSUME x = 0 PROVE y = 0
         PROVE [](x = 0 => y = 0)
BY PTL

=============================================================================
stderr: status:failed
stderr: prover:ls4
stderr: reason:false
nostderr: status:proved
nostderr: Unexpected error
nostderr: Unexpected exception
nostd*: ending abnormally
