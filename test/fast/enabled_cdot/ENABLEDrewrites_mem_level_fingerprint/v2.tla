--------------- MODULE temp --------------
EXTENDS TLAPS


VARIABLE x


A == x'


THEOREM (ENABLED (x' \in A)) = (A # {})
BY ENABLEDrewrites

================================================================================
