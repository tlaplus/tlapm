------ MODULE identity1_test ------

(*****************************************************************************)
(* Name: identity1_test                                                      *)
(* Author: Antoine Defourné                                                  *)
(* Date: 16/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

Id(S) == [ x \in S |-> x ]

THEOREM ASSUME NEW S
        PROVE \A x \in S : Id([S -> S])[ Id(S) ][x] = x
    BY DEF Id

====

