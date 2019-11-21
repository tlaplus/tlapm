------ MODULE composition_test ------

(*****************************************************************************)
(* Name: composition_test                                                    *)
(* Author: Antoine Defourné                                                  *)
(* Date: 19/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

g \o f == [ x \in DOMAIN f |-> g[f[x]] ]

THEOREM ASSUME NEW A,
               NEW B,
               NEW C,
               NEW f \in [ A -> B ],
               NEW g \in [ B -> C ]
        PROVE g \o f \in [ A -> C ]
    BY DEF \o

====

