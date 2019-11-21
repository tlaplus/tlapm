------ MODULE function2_test ------

(*****************************************************************************)
(* Name: function2_test                                                      *)
(* Author: Antoine Defourné                                                  *)
(* Date: 25/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW f \in [ A -> B ],
               NEW x \in A
        PROVE f[x] \in B
    OBVIOUS

====

