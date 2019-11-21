------ MODULE firstorder2_test ------

(*****************************************************************************)
(* Name: firstorder2_test                                                    *)
(* Author: Antoine Defourné                                                  *)
(* Date: 01/07/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW P(_),
               NEW f(_, _),
               NEW g(_),
               NEW a,
               \A x : f(x, x) = g(x),
               P(f(a, a))
        PROVE P(g(a))
    OBVIOUS

====

