------ MODULE function13_test ------

(*****************************************************************************)
(* Name: function13_test                                                     *)
(* Author: Antoine Defourné                                                  *)
(* Date: 17/10/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW f,
               NEW x \in DOMAIN f,
               NEW E(_)
        PROVE [ f EXCEPT ![x] = E(x) ][x] = E(x)
    OBVIOUS

====

