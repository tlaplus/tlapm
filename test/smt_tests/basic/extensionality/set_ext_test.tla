------ MODULE set_ext_test ------

(*****************************************************************************)
(* Name: set_ext_test                                                        *)
(* Author: Antoine Defourné                                                  *)
(* Date: 01/07/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW x, NEW y,
               \A z : z \in x <=> z \in y
        PROVE x = y
    OBVIOUS

====

