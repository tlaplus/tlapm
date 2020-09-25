------ MODULE function12_test ------

(*****************************************************************************)
(* Name: function12_test                                                     *)
(* Author: Antoine Defourné                                                  *)
(* Date: 17/10/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW f,
               DOMAIN f = A,
               \A x \in A : f[x] \in B,
               NEW x \in A,
               NEW E(_),
               E(x) \in B
        PROVE [ f EXCEPT ![x] = E(x) ] \in [ A -> B ]
    OBVIOUS

====

