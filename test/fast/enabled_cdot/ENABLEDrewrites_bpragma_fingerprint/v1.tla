--------------- MODULE temp ----------------
(* Test that the names of proof directives that appear in the `BY` statement
are recorded in the fingerprint. Recording them ensures that changing the
proof directive(s) that is(are) listed in the `BY` statement also changes the
fingerprint of the proof obligation.

Previously, the names of proof directives (bpragmas) were not recorded in the
fingerprint. As a result, a proof obligation could be proved in a run of `tlapm`
and the proof directive then changed to a different one, for which the proof
obligation would not get proved, but the fingerprint remained unchanged, so
the proof obligation was erroneously proved by subsequent runs of `tlapm`.
*)
EXTENDS TLAPS


VARIABLE x


THEOREM ENABLED (x' = 1)
BY ENABLEDrewrites

================================================================================
