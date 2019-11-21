------ MODULE function24_test ------

(*****************************************************************************)
(* Name: function24_test                                                     *)
(* Author: Antoine Defourné                                                  *)
(* Date: 18/10/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW r \in [ foo : A, bar : B ],
               NEW a \in A
        PROVE [ r EXCEPT !.foo = a ].foo = a
    OBVIOUS

====

