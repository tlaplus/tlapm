-------------------------- MODULE ENABLEDrewrites_test -------------------------
(* Tests for the proof directive `ENABLEDrewrites`. *)
EXTENDS TLAPS


VARIABLES x, y, z, w


A == x
B == y'
C == x'


Rstate(i) == x
Raction(i) == x'
Sconstant == {1, 2}
Sstate == {x}


--------------------------------------------------------------------------------

THEOREM (ENABLED (\E i \in Sconstant:  Rstate(i))) =
    \E i \in Sconstant:  ENABLED Rstate(i)
BY ENABLEDrewrites


THEOREM (ENABLED (\E i \in Sstate:  Rstate(i))) =
    \E i \in Sstate:  ENABLED Rstate(i)
BY ENABLEDrewrites


THEOREM (ENABLED (\E i \in Sconstant:  Raction(i))) =
    \E i \in Sconstant:  ENABLED Raction(i)
BY ENABLEDrewrites


THEOREM (ENABLED (\E i \in Sstate:  Raction(i))) =
    \E i \in Sstate:  ENABLED Raction(i)
BY ENABLEDrewrites

--------------------------------------------------------------------------------

THEOREM (ENABLED (B \/ C)) = (ENABLED B \/ ENABLED C)
BY ENABLEDrewrites


THEOREM
    (ENABLED \/ A
             \/ B
             \/ C) =
    \/ ENABLED A
    \/ ENABLED B
    \/ ENABLED C
BY ENABLEDrewrites

--------------------------------------------------------------------------------

THEOREM (ENABLED (IF A THEN B ELSE C)) = IF A THEN ENABLED B ELSE ENABLED C
BY ENABLEDrewrites

--------------------------------------------------------------------------------

p1 == 1
p2 == x
a1 == x'
a2 == y'
b == x' /\ y'


THEOREM (ENABLED CASE p1 -> a1 [] p2 -> a2 [] OTHER -> b) =
    CASE p1 -> ENABLED a1 [] p2 -> ENABLED a2 [] OTHER -> ENABLED b
BY ENABLEDrewrites

--------------------------------------------------------------------------------

c1 == x
c2 == y
c3 == z
c4 == w

c5 == x'
c6 == y'
c7 == z'
c8 == w'

c9 == x' /\ y'
c10 == z' /\ w'


THEOREM (ENABLED (c1 /\ c2)) = (ENABLED c1 /\ ENABLED c2)
BY ENABLEDrewrites


THEOREM (ENABLED (c1 /\ c2 /\ c3 /\ c4)) =
    (ENABLED c1 /\ ENABLED c2 /\ ENABLED c3 /\ ENABLED c4)
BY ENABLEDrewrites


THEOREM (ENABLED (c1 /\ c6)) = (ENABLED c1 /\ ENABLED c6)
BY ENABLEDrewrites DEF c6


THEOREM (ENABLED (c5 /\ c6 /\ c7 /\ c8)) =
    (ENABLED c5 /\ ENABLED c6 /\ ENABLED c7 /\ ENABLED c8)
BY ENABLEDrewrites DEF c5, c6, c7, c8


THEOREM (ENABLED (c5 /\ c6 /\ c9)) = /\ ENABLED /\ y'
                                                /\ y'
                                     /\ ENABLED /\ x'
                                                /\ x'
BY ENABLEDrewrites DEF c5, c6, c9


THEOREM (ENABLED (c9 /\ c10)) = /\ ENABLED x'
                                /\ ENABLED y'
                                /\ ENABLED z'
                                /\ ENABLED w'
BY ENABLEDrewrites DEF c9, c10

--------------------------------------------------------------------------------

THEOREM (ENABLED x) = x
BY ENABLEDrewrites

--------------------------------------------------------------------------------

THEOREM ENABLED (x' = 1)
BY ENABLEDrewrites

--------------------------------------------------------------------------------

S == {z, w}


THEOREM (ENABLED (x' \in S)) = (S # {})
BY ENABLEDrewrites

--------------------------------------------------------------------------------

THEOREM (ENABLED (ENABLED (B /\ C))') =
    ENABLED ((/\ ENABLED C
              /\ ENABLED B)')
BY ENABLEDrewrites DEF B, C


THEOREM Foo == ENABLED (A /\ B) <=> (x /\ ENABLED B)
BY ENABLEDrewrites DEF A, B


THEOREM Bar == (x /\ ENABLED B) <=> x
BY ExpandENABLED DEF B


THEOREM FooBar == ENABLED (A /\ B) <=> x
BY Foo, Bar


C == x'
D == y'


THEOREM ENABLED (C /\ D) <=> (ENABLED C /\ ENABLED D)
BY ENABLEDrewrites DEF C, D


================================================================================
