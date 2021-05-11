------ MODULE identity2_test ------

(*****************************************************************************)
(* Name: identity2_test                                                      *)
(* Author: Antoine Defourné                                                  *)
(* Date: 16/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW Id(_),
               \A S : Id(S) = [ x \in S |-> x ],
               NEW S
        PROVE \A x \in S : Id([S -> S])[ Id(S) ][x] = x
    OBVIOUS

====

