-------------------------- MODULE ExpandENABLED_LET_test -----------------------
(* Unit test of `ExpandENABLED` with `LET` in proof obligation. *)
EXTENDS TLAPS


THEOREM
    ASSUME VARIABLE x
    PROVE
        LET
            Foo(r) == r
        IN
            x => ENABLED /\ Foo(x)
                         /\ Foo(x')
PROOF
    BY ExpandENABLED, Zenon
================================================================================
