------ MODULE tuple2_test ------

(*****************************************************************************)
(* Name: tuple2_test                                                         *)
(* Author: Antoine Defourné                                                  *)
(* Date: 24/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW x \in A,
               NEW y \in B
        PROVE <<x, y>> \in A \X B
    OBVIOUS

====


