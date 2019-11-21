------ MODULE record_as_function_test ------

(*****************************************************************************)
(* Name: record_as_function_test                                             *)
(* Author: Antoine Defourné                                                  *)
(* Date: 25/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS, Integers

R == [ foo : Int,
       bar : Int
     ]

THEOREM \A r \in R : \A s \in { "foo", "bar" } : r[s] \in Int
    BY DEF R

====

