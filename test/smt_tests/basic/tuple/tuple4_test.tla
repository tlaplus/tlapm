------ MODULE tuple4_test ------

(*****************************************************************************)
(* Name: tuple4_test                                                         *)
(* Author: Antoine Defourné                                                  *)
(* Date: 25/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW x
        PROVE <<x, x>> = <<x, x>>
    OBVIOUS

====


