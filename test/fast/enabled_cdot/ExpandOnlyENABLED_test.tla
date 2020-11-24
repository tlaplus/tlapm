-------------------------- MODULE ExpandOnlyENABLED_test -----------------------
(* Test with `ExpandENABLED` and `\cdot` occurs in scope of `ENABLED`.

The proof directive `ExpandCdot` is not given.
*)
EXTENDS TLAPS


THEOREM ENABLED (TRUE \cdot TRUE)
BY ExpandENABLED
================================================================================
stderr: status:failed
