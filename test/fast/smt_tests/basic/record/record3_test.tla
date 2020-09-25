------ MODULE record3_test ------

(*****************************************************************************)
(* Name: record3_test                                                         *)
(* Author: Antoine Defourné                                                  *)
(* Date: 25/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW a,
               NEW b
        PROVE DOMAIN [ foo |-> a, bar |-> b ] = { "foo", "bar" }
    OBVIOUS

====

