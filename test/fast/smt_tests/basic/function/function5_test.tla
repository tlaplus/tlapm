------ MODULE function5_test ------

(*****************************************************************************)
(* Name: function5_test                                                      *)
(* Author: Antoine Defourné                                                  *)
(* Date: 25/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW C,
               B \subseteq C
        PROVE [ A -> B ] \subseteq [ A -> C ]
    OBVIOUS

====

