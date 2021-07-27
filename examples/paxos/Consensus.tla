----------------------------- MODULE Consensus -----------------------------
(***************************************************************************)
(* This is a trivial specification of consensus.  It asserts that the      *)
(* variable `chosen', which represents the set of values that someone      *)
(* might think has been chosen is initially empty and can be changed only  *)
(* by adding a single element to it.                                       *)
(***************************************************************************)
CONSTANTS Acceptors, Values

VARIABLE chosen

Init == chosen = {}

Next == /\ chosen = {}
        /\ \E v \in Values : chosen' = chosen \cup {v}
        
Spec == Init /\ [][Next]_chosen

=============================================================================
\* Modification History
\* Last modified Wed Nov 21 11:35:33 PST 2012 by lamport
\* Created Mon Nov 19 15:19:09 PST 2012 by lamport
