------------- MODULE temp --------------
(* Test that changing the level of the bound in `\E` also changes the result of
the proof directive `ENABLEDrewrites`.
*)
EXTENDS TLAPS


VARIABLE x


R(i) == x'
C == {1, 2}
W == {x'}


THEOREM (ENABLED (\E i \in C:  R(i))) = \E i \in C:  ENABLED R(i)
BY ENABLEDrewrites

================================================================================
