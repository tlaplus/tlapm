------------------------ MODULE ExpandOnlyCdot_test ----------------------------
(* Test with `ExpandCdot` and `ENABLED` occurs in scope of `\cdot`.

The proof directive `ExpandENABLED` is not given.
*)
EXTENDS TLAPS


THEOREM ((ENABLED TRUE) \cdot TRUE)
BY ExpandCdot
================================================================================
stderr: status:failed
