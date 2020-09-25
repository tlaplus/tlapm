------ MODULE choice_axiom_test ------

(*****************************************************************************)
(* Name: choice_axiom_test                                                   *)
(* Author: Antoine Defourné                                                  *)
(* Date: 13/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM \A a : {} \notin a => \E f \in [ a -> UNION a ] : \A x \in a : f[x] \in x
<1> TAKE a
<1>1 HAVE {} \notin a
<1> DEFINE f == [ x \in a |-> CHOOSE y : y \in x ]
<1>2 DOMAIN f = a
    OBVIOUS
<1>3 \A x \in a : f[x] \in UNION a
    BY <1>1
<1> WITNESS f \in [ a -> UNION a ]
<1>4 \A x \in a : f[x] \in x
    BY <1>1
<1> QED
    BY <1>4

====

