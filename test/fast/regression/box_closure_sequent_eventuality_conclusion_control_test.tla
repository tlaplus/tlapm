-------------- MODULE box_closure_sequent_eventuality_conclusion_control_test --------------

\* x stays 0, and y is 0 initially and then 1 forever.

EXTENDS TLAPS

VARIABLES x, y

THEOREM ASSUME ASSUME x = 0 PROVE <>(y = 0)
         PROVE [](x = 0 => <>(y = 0))
BY PTL

=============================================================================
stderr: status:failed
stderr: prover:ls4
stderr: reason:false
nostderr: status:proved
nostderr: Unexpected error
nostderr: Unexpected exception
nostd*: ending abnormally
