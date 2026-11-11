-------------- MODULE box_closure_sequent_control_test --------------

\* A state formula is not box-closed. x is 0 and then 1.

EXTENDS TLAPS

VARIABLE x

THEOREM ASSUME x = 0 PROVE [](x = 0)
BY PTL

=============================================================================
stderr: status:failed
stderr: prover:ls4
stderr: reason:false
nostderr: status:proved
nostderr: Unexpected error
nostderr: Unexpected exception
nostd*: ending abnormally
