------ MODULE function14_test ------

(*****************************************************************************)
(* Name: function14_test                                                     *)
(* Author: Antoine Defourné                                                  *)
(* Date: 17/10/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW f,
               NEW x \in DOMAIN f,
               NEW y,
               y /= x,
               NEW E(_)
        PROVE [ f EXCEPT ![y] = E(y) ][x] = f[x]
    OBVIOUS

====

