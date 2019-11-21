------ MODULE function15_test ------

(*****************************************************************************)
(* Name: function15_test                                                     *)
(* Author: Antoine Defourné                                                  *)
(* Date: 17/10/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW f,
               NEW x \in DOMAIN f,
               NEW y \in DOMAIN f[x],
               NEW u \in DOMAIN f,
               NEW v \in DOMAIN f[u],
               NEW z,
               NEW w
        PROVE DOMAIN [ f EXCEPT ![x][y] = z, ![u][v] = w ] = DOMAIN f
    OBVIOUS

====

