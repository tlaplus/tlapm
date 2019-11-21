------ MODULE function3_test ------

(*****************************************************************************)
(* Name: function3_test                                                      *)
(* Author: Antoine Defourné                                                  *)
(* Date: 25/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW f,
               DOMAIN f = A,
               \A x \in A : f[x] \in B
        PROVE f \in [ A -> B ]
    OBVIOUS

====

