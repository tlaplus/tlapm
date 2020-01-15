------ MODULE ifxeqtrue_test ------

(*****************************************************************************)
(* Name: If x Equals TRUE                                                    *)
(* Author: Antoine Defourné                                                  *)
(*    a non-sensical formula.                                                *)
(* Date: 01/07/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM \A x : IF x = TRUE THEN x ELSE TRUE
    OBVIOUS

====

