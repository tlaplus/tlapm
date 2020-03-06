------ MODULE quantifiers_test ------

(*****************************************************************************)
(* Name: quantifiers_test                                                    *)
(* Author: Hernán Vanzetto                                                   *)
(* Date: 26/02/2020                                                          *)
(*****************************************************************************)

EXTENDS TLAPS

LEMMA ASSUME NEW S PROVE \A x \in S: TRUE
OBVIOUS

LEMMA (\A x: FALSE) = FALSE
OBVIOUS

LEMMA ASSUME NEW S PROVE (\E x \in S: FALSE) = FALSE
OBVIOUS

LEMMA \E x: TRUE
OBVIOUS

LEMMA ASSUME NEW P PROVE (\E x \in {}: P) = FALSE
OBVIOUS

LEMMA ASSUME NEW P PROVE \A x \in {}: P
OBVIOUS

====
