------ MODULE function11_test ------

(*****************************************************************************)
(* Name: function11_test                                                     *)
(* Author: Antoine Defourné                                                  *)
(* Date: 17/10/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW f \in [ A -> B ],
               NEW x \in A,
               NEW y \in A,
               NEW E(_),
               E(x) \in B
        PROVE [ f EXCEPT ![x] = E(x) ][y] \in B
    OBVIOUS

====

