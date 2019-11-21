------ MODULE tuple5_test ------

(*****************************************************************************)
(* Name: tuple5_test                                                         *)
(* Author: Antoine Defourné                                                  *)
(* Date: 25/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW x,
               NEW y,
               x /= y
        PROVE <<x, y>> /= <<y, x>>
    OBVIOUS

====


