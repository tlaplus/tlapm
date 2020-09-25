------ MODULE tuple7_test ------

(*****************************************************************************)
(* Name: tuple7_test                                                         *)
(* Author: Antoine Defourné                                                  *)
(* Date: 25/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW x,
               NEW y,
               NEW z,
               NEW u,
               NEW v,
               NEW w,
               NEW t
        PROVE <<x, y, z>> /= <<u, v, w, t>>
    OBVIOUS

====


