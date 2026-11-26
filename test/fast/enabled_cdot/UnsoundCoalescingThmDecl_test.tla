--------------------- MODULE UnsoundCoalescingThmDecl_test ---------------------
(* An example of substituting an action-level expression for a state predicate
by using coalescing, leading to an unsound proof.
*)
EXTENDS TLAPS


THEOREM
    ASSUME
        VARIABLE x,
        x'
    PROVE
        FALSE
PROOF
<1> HIDE x'
<1>1. ASSUME STATE P
      PROVE (ENABLED (P /\ ~ x'))  <=>  (P /\ ENABLED (~ x'))
    BY ENABLEDaxioms
<1> DEFINE P == ~ ~ x'
<1> HIDE DEF P
<1>2. (ENABLED (P /\ ~ x'))  <=>  (P /\ ENABLED (~ x'))
    BY <1>1  (* This proof is unsound. *)
             (* This proof fails if coalescing prepends the kind
             of declaration to all operator names.
             *)
<1> QED
    BY <1>2, x', ExpandENABLED DEF P

================================================================================
stderr: obligations failed
