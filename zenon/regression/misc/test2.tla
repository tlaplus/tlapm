---------------------------- MODULE test2 ----------------------------
CONSTANT Set, A, B

P(x) == x
Q(x) == {}
THEOREM THM1 == A = {x \in Set : P(x)}
THEOREM THM2 == B = {x \in Set : Q(x)}

THEOREM A \subseteq B <=> \A x \in Set : P(x) => Q(x)
PROOF <1>1. {x \in Set : P(x)} \subseteq {x \in Set : Q(x)}
               <=> \A x \in Set : P(x) => Q(x)
   \* ETLA produces a parsing error  ^ here
          PROOF OBVIOUS
      <1>2. QED
           PROOF BY <1>1, THM1, THM2 DEF THM1, THM2 \* DEF A, B
======================================================================
