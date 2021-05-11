------ MODULE firstorder6_test ------

(*****************************************************************************)
(* Name: firstorder6_test                                                    *)
(* Author: Antoine Defourné                                                  *)
(* Date: 15/07/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW P(_, _),
               \E x : \A y : P(x, y)
        PROVE \A z : \E w : P(w, z)
<1>1 PICK x : \A y : P(x, y)
    OBVIOUS
<1>2 TAKE z
<1>3 WITNESS x
<1> QED
    BY ONLY <1>1

====

