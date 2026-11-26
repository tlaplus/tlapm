---- MODULE temp ----
(* Test that proof obligations with AutoUSE
are fingerprinted after automated expansion
of definitions.

Run `tlapm` to create fingerprints,
edit the input file to make the proof obligation unprovable,
and re-run `tlapm` to ensure that the saved fingerprint does
not shadow the change of the defined operator `A` that is
expanded by `AutoUSE`.
*)
EXTENDS TLAPS


VARIABLE x


A == x' = 1


THEOREM ENABLED A
BY ExpandENABLED, AutoUSE

====================================
