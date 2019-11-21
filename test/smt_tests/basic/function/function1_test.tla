------ MODULE function1_test ------

(*****************************************************************************)
(* Name: function1_test                                                      *)
(* Author: Antoine Defourné                                                  *)
(* Date: 25/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW f \in [ A -> B ]
        PROVE DOMAIN f = A
    OBVIOUS

====

