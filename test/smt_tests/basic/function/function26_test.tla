------ MODULE function26_test ------

(*****************************************************************************)
(* Name: function26_test                                                     *)
(* Author: Antoine Defourné                                                  *)
(* Date: 18/10/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW C,
               NEW f \in [ A -> [ foo : B, bar : C ] ],
               NEW x \in A,
               NEW E(_),
               E(x) \in C
        PROVE DOMAIN [ f EXCEPT ![x].bar = E(x) ] = A
    OBVIOUS

====

