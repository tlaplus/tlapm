------ MODULE function8_test ------

(*****************************************************************************)
(* Name: function8_test                                                      *)
(* Author: Antoine Defourné                                                  *)
(* Date: 26/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW C,
               NEW F(_, _, _, _)
        PROVE DOMAIN [ x \in A, y, z \in B, u \in C |-> F(x, y, z, u) ] = A \X B \X B \X C
    OBVIOUS

====

