-------------- MODULE temp --------------
EXTENDS TLAPS


VARIABLE x


p1 == x'
a1 == x'


THEOREM (ENABLED CASE p1 -> a1) = CASE p1 -> ENABLED a1
BY ENABLEDrewrites

================================================================================
