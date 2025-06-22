------------- MODULE temp --------------
EXTENDS TLAPS


VARIABLE x


R(i) == x'
C == {1, 2}
W == {x'}


THEOREM (ENABLED (\E i \in W:  R(i))) = \E i \in W:  ENABLED R(i)
BY ENABLEDrewrites

================================================================================
