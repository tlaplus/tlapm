------ MODULE firstorder1_test ------

(*****************************************************************************)
(* Name: firstorder1_test                                                    *)
(* Author: Antoine Defourné                                                  *)
(* Date: 01/07/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW P(_, _),
               NEW a,
               NEW b,
               \A x, y : P(x, y) => P(y, a),
               P(b, a)
        PROVE P(a, a)
    OBVIOUS

====

