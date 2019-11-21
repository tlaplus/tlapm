------ MODULE empty_set_ext_test ------

(*****************************************************************************)
(* Name: empty_set_ext_test                                                  *)
(* Author: Antoine Defourné                                                  *)
(* Date: 22/10/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW S,
               \A x : x \notin S
        PROVE S = {}
    OBVIOUS

====

