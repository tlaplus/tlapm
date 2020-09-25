------ MODULE record2_test ------

(*****************************************************************************)
(* Name: record2_test                                                         *)
(* Author: Antoine Defourné                                                  *)
(* Date: 25/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW a \in A,
               NEW b \in B
        PROVE [ foo |-> a, bar |-> b ] \in [ foo : A, bar : B ]
    OBVIOUS

====

