------ MODULE app_ambiguity_test ------

(*****************************************************************************)
(* Name: app_ambiguity_test                                                  *)
(* Author: Antoine Defourné                                                  *)
(* Date: 22/10/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A, NEW B
        PROVE \A h : h \in (A \X B) \cup [ {1, 2} -> A ] => h[1] \in A
    OBVIOUS

====

