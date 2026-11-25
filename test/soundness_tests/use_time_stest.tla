------------- MODULE use_time_stest --------------

\* USE b proves b from the assumption, which holds only now, so the fact
\* b must not get the time Always just because b is not the name of a
\* fact: PTL would receive it as []b.  The theorem is false for a
\* behavior where b is TRUE and then FALSE.

EXTENDS TLAPS

VARIABLE b

THEOREM ASSUME b PROVE []b
<1> USE b
<1> QED
    BY PTL

============================================================
