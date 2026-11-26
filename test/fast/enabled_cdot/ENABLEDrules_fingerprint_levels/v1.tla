---- MODULE temp ----
(* Test that fingerprints do not mask change of level
of a proof step.

Run `tlapm` to create fingerprints.
Then, edit this file to change the level of an assumption
from state predicate to action. Re-run `tlapm` to ensure
that the saved fingerprint does not shadow the change of
the level of the assumption, at the proof step that
includes `ENABLEDrules`.
*)
EXTENDS TLAPS


VARIABLE x


THEOREM
    ASSUME x = 1
    PROVE ENABLED (x' = 1) => ENABLED (x' = 1 \/ x' = 2)
<1>1. (x' = 1) => (x' = 1 \/ x' = 2)
    OBVIOUS
<1> QED
    BY ONLY <1>1, ENABLEDrules


=====================================================
