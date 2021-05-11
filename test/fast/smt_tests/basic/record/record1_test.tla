------ MODULE record1_test ------

(*****************************************************************************)
(* Name: record1_test                                                         *)
(* Author: Antoine Defourné                                                  *)
(* Date: 25/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW C,
               NEW r \in [ foo : A, bar : B, baz : C ]
        PROVE r.foo \in A /\ r.bar \in B /\ r.baz \in C
    OBVIOUS

====

