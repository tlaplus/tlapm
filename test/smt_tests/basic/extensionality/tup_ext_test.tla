------ MODULE tup_ext_test ------

(*****************************************************************************)
(* Name: tup_ext_test                                                        *)
(* Author: Antoine Defourné                                                  *)
(* Date: 22/10/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW t \in A \X B
        PROVE t = <<t[1], t[2]>>
    OBVIOUS

====

