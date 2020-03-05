---------------------------- MODULE test1 ----------------------------
CONSTANT Set

P(x) == x
Q(x) == {}
A == {x \in Set : P(x)}
B == {x \in Set : Q(x)}

THEOREM A \cup B = {x \in Set : P(x) \/ Q(x)}
PROOF <1>1.  {x \in Set : P(x)} \cup {x \in Set : Q(x)}
               = {x \in Set : P(x) \/ Q(x)}
           PROOF OBVIOUS
      <1>2. QED
           PROOF BY <1>1 DEF A, B
======================================================================
