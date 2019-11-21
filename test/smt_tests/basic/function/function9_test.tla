------ MODULE function9_test ------

(*****************************************************************************)
(* Name: function9_test                                                      *)
(* Author: Antoine Defourné                                                  *)
(* Date: 16/10/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW C,
               NEW F(_, _, _),
               NEW x \in A,
               NEW y \in B,
               NEW z \in C
       PROVE [ u \in A, v \in B, w \in C |-> F(x, y, z) ][x, y, z] = F(x, y, z)
    OBVIOUS

====

