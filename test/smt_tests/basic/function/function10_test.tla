------ MODULE function10_test ------

(*****************************************************************************)
(* Name: function10_test                                                     *)
(* Author: Antoine Defourné                                                  *)
(* Date: 17/10/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW f \in [ A -> B ],
               NEW x \in A,
               NEW E(_),
               E(x) \in B
        PROVE DOMAIN [ f EXCEPT ![x] = E(x) ] = A
    OBVIOUS

====

