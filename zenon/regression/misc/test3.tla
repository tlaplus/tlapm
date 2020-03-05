------------------- MODULE test3 --------------

CONSTANT flag

(***
THEOREM (flag \in [{0,1} -> BOOLEAN]) =>
           \A i \in {0,1} : flag[i] \in BOOLEAN
****)
THEOREM (flag \in [{0,1} -> BOOLEAN]) =>
           flag[0] \in BOOLEAN
PROOF <1>1.   0 \in {0,1}
            PROOF OBVIOUS
      <1>  QED
           PROOF BY <1>1
=============================================================================
