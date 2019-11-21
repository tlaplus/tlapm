------ MODULE function27_test ------

(*****************************************************************************)
(* Name: function27_test                                                     *)
(* Author: Antoine Defourné                                                  *)
(* Date: 18/10/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW C,
               NEW f \in [ A -> [ foo : B, bar : C ] ],
               NEW x \in A,
               NEW y \in A,
               NEW E(_),
               E(x) \in B
        PROVE [ f EXCEPT ![x].foo = E(x) ][y] \in [ foo : B, bar : C ]
    OBVIOUS

====

