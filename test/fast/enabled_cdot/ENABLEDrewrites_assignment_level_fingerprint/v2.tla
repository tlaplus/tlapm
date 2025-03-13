------------ MODULE temp ----------
EXTENDS TLAPS


VARIABLE x


A == x'


THEOREM (ENABLED (x' = A)) = TRUE
BY ENABLEDrewrites

================================================================================
