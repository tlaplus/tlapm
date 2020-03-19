------ MODULE russell_test ------

(*****************************************************************************)
(* Name: russell_test                                                        *)
(* Author: Antoine Defourné                                                  *)
(* Date: 16/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW V,
               \A x : x \in V
        PROVE FALSE
<1> DEFINE R == { x \in V : x \notin x }
<1> HIDE DEF R
<1>1 R \in R <=> R \notin R
    <2>1 R \in R => R \notin R
        BY DEF R
    <2>2 R \notin R => R \in R
        BY DEF R
    <2> QED
        BY ONLY <2>1, <2>2
<1> QED
    BY ONLY <1>1

====

