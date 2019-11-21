------ MODULE tuple3_test ------

(*****************************************************************************)
(* Name: tuple3_test                                                         *)
(* Author: Antoine Defourné                                                  *)
(* Date: 24/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW s \in A \X B
        PROVE s[1] \in A /\ s[2] \in B
    OBVIOUS

====


