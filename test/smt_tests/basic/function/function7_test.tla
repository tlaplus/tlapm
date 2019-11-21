------ MODULE function7_test ------

(*****************************************************************************)
(* Name: function7_test                                                      *)
(* Author: Antoine Defourné                                                  *)
(* Date: 25/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW F(_)
        PROVE DOMAIN [ x \in A |-> F(x) ] = A
    OBVIOUS

====

