------------- MODULE have_time_stest --------------

\* HAVE x = 0 must not give the new fact x = 0 the time of the enclosing
\* scope, which is Always: PTL would receive it as [](x = 0) although it
\* holds only now.  The theorem is false for a behavior where x changes
\* from 0 to 1.

EXTENDS TLAPS

VARIABLE x

THEOREM x = 0 => (x = 0)'
<1> HAVE x = 0
<1>1. [](x = 0)
    BY PTL
<1> QED
    BY <1>1, PTL

============================================================
