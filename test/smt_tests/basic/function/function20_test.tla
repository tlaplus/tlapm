------ MODULE function20_test ------

(*****************************************************************************)
(* Name: function20_test                                                     *)
(* Author: Antoine Defourné                                                  *)
(* Date: 18/10/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW r \in [ foo : A, bar : B ],
               NEW a \in A
        PROVE DOMAIN [ r EXCEPT !.foo = a ] = { "foo", "bar" }
    OBVIOUS

====

