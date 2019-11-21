------ MODULE nonempty_integer_test ------

(*****************************************************************************)
(* Name: nonempty_integer_test                                               *)
(* Author: Antoine Defourné                                                  *)
(* Date: 25/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS, Integers

THEOREM \E z \in Int : \E x : x \in z
<1>1 SUFFICES ASSUME \A z \in Int : z = {}
              PROVE FALSE
    OBVIOUS
<1>2 0 = {}
    BY <1>1
<1>3 @ = 1
    BY <1>1
<1> QED
    BY ONLY <1>2, <1>3

====

