------ MODULE function23_test ------

(*****************************************************************************)
(* Name: function23_test                                                     *)
(* Author: Antoine Defourné                                                  *)
(* Date: 18/10/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW r \in [ foo : A, bar : B ],
               NEW a \in A
        PROVE [ r EXCEPT !.foo = a ] \in [ foo : A, bar : B ]
    OBVIOUS

====

