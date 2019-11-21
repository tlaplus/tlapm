------ MODULE function18_test ------

(*****************************************************************************)
(* Name: function18_test                                                     *)
(* Author: Antoine Defourné                                                  *)
(* Date: 17/10/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW f,
               NEW x \in DOMAIN f,
               NEW y \in DOMAIN f[x],
               NEW v \in DOMAIN f[x],
               NEW z,
               NEW w
        PROVE [ f EXCEPT ![x][y] = z, ![x][v] = w ][x] =
                [ [ f[x] EXCEPT ![y] = z ] EXCEPT ![v] = w ]
    OBVIOUS

====

