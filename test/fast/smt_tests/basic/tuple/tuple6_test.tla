------ MODULE tuple6_test ------

(*****************************************************************************)
(* Name: tuple6_test                                                         *)
(* Author: Antoine Defourné                                                  *)
(* Date: 25/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW x,
               NEW y,
               NEW u,
               NEW v,
               <<x, y>> = <<u, v>>
        PROVE x = u /\ y = v
    OBVIOUS

====


