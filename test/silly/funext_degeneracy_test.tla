------ MODULE funext_degeneracy_test ------

EXTENDS TLAPS

(* This theorem relies on a set of axioms that are stronger than those
 * introduced in Specifying Systems.  It may not be desirable to have
 * it actually provable. *)

THEOREM FuncSet ==
        ASSUME NEW x
        PROVE \E a, b : x \in [ a -> b ]
<1> DEFINE a == DOMAIN x
<1> DEFINE b == { x[y] : y \in a }
<1> HIDE DEF a, b
<1>1 DOMAIN x = a       BY DEF a
<1>2 ASSUME NEW y \in a
     PROVE x[y] \in b   BY DEF b
<1> QED                 BY ONLY <1>1, <1>2

THEOREM ASSUME NEW x,
               NEW y,
               DOMAIN x = DOMAIN y,
               \A z \in DOMAIN x : x[z] = y[z]
        PROVE x = y
<1>1 PICK ax, bx : x \in [ ax -> bx ]   BY FuncSet
<1>2 PICK ay, by : y \in [ ay -> by ]   BY FuncSet
<1>3 ax = ay                            BY <1>1, <1>2
<1> DEFINE a == ax
<1> DEFINE b == bx \cup by
<1>4 x \in [ a -> b ]                   BY <1>1
<1>5 y \in [ a -> b ]                   BY <1>2, <1>3
<1> QED                                 BY <1>4, <1>5

====

