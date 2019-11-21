------ MODULE function22_test ------

(*****************************************************************************)
(* Name: function22_test                                                     *)
(* Author: Antoine Defourné                                                  *)
(* Date: 18/10/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW r \in [ foo : A, bar : B ],
               NEW a \in A
        PROVE [ r EXCEPT !.foo = a ].bar \in B
    OBVIOUS

====

