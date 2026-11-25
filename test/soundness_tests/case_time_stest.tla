------------- MODULE case_time_stest --------------

\* CASE x = 0 must not give the case assumption x = 0 the time of the
\* enclosing scope, which is Always: PTL would receive it as [](x = 0)
\* although it holds only now.  The theorem is false for a behavior where
\* x changes from 0 to 1.

EXTENDS TLAPS

VARIABLE x

THEOREM x = 0 => (x = 0)'
<1>1. CASE x = 0
    <2>1. [](x = 0)
        BY <1>1, PTL
    <2> QED
        BY <2>1, PTL
<1> QED
    BY <1>1

============================================================
