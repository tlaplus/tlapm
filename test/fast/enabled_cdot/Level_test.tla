------------------------------ MODULE Level_test -------------------------------
(* Tests for computing expression levels. *)
EXTENDS TLAPS, Integers, TLC


CONSTANT c
VARIABLES x, y


P == ENABLED (x')

f(g) == TRUE
h(r, w) == TRUE

Q == /\ IF x THEN x' ELSE c
     /\ 1 + 2
        (* {r \in S:  P(r)} set such that *)
     /\ {r \in {1, 2}:  TRUE}
     /\ {r \in {1, 2}:  c}
     /\ {r \in {1, 2}:  x}
     /\ {r \in {1, 2}:  x'}
     /\ {r \in {1, 2}:  r + 1}
     /\ {r \in {1, 2}:  r + x}
     /\ {r \in {1, 2}:  r + x'}
     /\ {r \in x:  TRUE}
     /\ {r \in x':  TRUE}
        (* {f(z):  z \in S} *)
     /\ {f(g):  g \in x}
     /\ {f(g):  g \in x'}
     /\ {h(z, w):  z \in x,  w \in x'}
        (* {1, 2, 3} set enumeration *)
     /\ {1, 2, 3}
     /\ {c, 1}
     /\ {c, x}
     /\ {x, 1}
     /\ {x, x'}
     /\ {x', 1}
     /\ {c, x'}
     /\ {c, x, x'}
        (* Tuples *)
     /\ << 1, 2, 3 >>
     /\ << c, 1, 2 >>
     /\ << x, 1, 2 >>
     /\ << x, 1, c >>
     /\ << x, x', c >>
        (* Function application *)
     /\ 1[1]
     /\ c[1]
     /\ x[1]
     /\ x[c]
     /\ x[x']
     /\ (x')[x]
        (* [f EXCEPT ![1] = 2] *)
     /\ [c EXCEPT ![1] = 2]
     /\ [c EXCEPT ![x] = 2]
     /\ [c EXCEPT ![x'] = 2]
     /\ [c EXCEPT ![1] = x]
     /\ [c EXCEPT ![1] = x']

     /\ [x EXCEPT ![1] = 2]
     /\ [x EXCEPT ![c] = 2]
     /\ [x EXCEPT ![x] = 2]
     /\ [x EXCEPT ![x'] = 2]

     /\ [x EXCEPT ![1] = c]
     /\ [x EXCEPT ![1] = x]
     /\ [x EXCEPT ![1] = x']

     /\ [x' EXCEPT ![1] = 2]
     /\ [x' EXCEPT ![c] = 2]
     /\ [x' EXCEPT ![x] = 2]
     /\ [x' EXCEPT ![x'] = 2]

     /\ [x' EXCEPT ![1] = c]
     /\ [x' EXCEPT ![1] = x]
     /\ [x' EXCEPT ![1] = x']
        (* rigid quantification *)
     /\ \E r:  r
     /\ \E r \in {1}:  r
     /\ \E r, w:  r /\ w
     /\ \E r \in {1}, w \in {1}:  r /\ w
     /\ \E r \in {1}, w \in {2}:  r /\ w
     /\ \E r, w \in {1}:  r /\ w
     /\ \E r \in {1, 2}:  r
     /\ \E r \in x:  r
     /\ \E r \in x':  r
     /\ \E r:  c
     /\ \E r:  x
     /\ \E r:  x'
     /\ \E r, w:  x'
        (* CHOOSE *)
     /\ CHOOSE r:  r = 1
        (* ENABLED *)
     /\ ENABLED c
     /\ ENABLED x
     /\ ENABLED (x + 1)
     /\ ENABLED (x')
     /\ ENABLED (x + x')
        (* [A]_e *)
     /\ [x' = x + 1]_x
        (* << A >>_e *)
     /\ << x' = x + 1 >>_x
     /\ UNCHANGED x
     /\ UNCHANGED << x, y >>

     /\ LET R(w) == TRUE
        IN R(TRUE)
     /\ Print(1, "message")
     /\ Assert(1, "message")
     /\ JavaTime
     /\ {1} :> 2
     /\ 1 @@ 2
     /\ Permutations({1, 2, 3})


THEOREM ENABLED Q
PROOF
    BY ExpandENABLED DEF Q


THEOREM SortSeq(<<1, 2, 3>>, <)
OBVIOUS

================================================================================
stderr: status:failed
