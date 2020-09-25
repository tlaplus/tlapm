------ MODULE fun_ext_test ------

(*****************************************************************************)
(* Name: fun_ext_test                                                        *)
(* Author: Antoine Defourné                                                  *)
(* Date: 22/10/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW f \in [ A -> B ]
        PROVE f = [ x \in DOMAIN f |-> f[x] ]
    OBVIOUS

====

