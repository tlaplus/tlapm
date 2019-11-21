------ MODULE prop12_test ------

(*****************************************************************************)
(* Name: prop12_test                                                         *)
(* Author: Antoine Defourné                                                  *)
(* Date: 01/07/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A \in BOOLEAN,
               NEW B \in BOOLEAN,
               NEW C \in BOOLEAN
        PROVE (A \/ B) /\ C <=> (A /\ C) \/ (B /\ C)
    OBVIOUS

====

