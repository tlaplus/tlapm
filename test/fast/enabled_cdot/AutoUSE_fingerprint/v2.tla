---- MODULE temp ----
EXTENDS TLAPS


VARIABLE x


A == x' # x'


THEOREM ENABLED A
BY ExpandENABLED, AutoUSE

====================================
