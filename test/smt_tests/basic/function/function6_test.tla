------ MODULE function6_test ------

(*****************************************************************************)
(* Name: function6_test                                                      *)
(* Author: Antoine Defourné                                                  *)
(* Date: 25/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW F(_),
               NEW x \in A
        PROVE [ y \in A |-> F(y) ][x] = F(x)
    OBVIOUS

====

