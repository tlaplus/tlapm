---- MODULE capcard2_test ----

EXTENDS TLAPS, FiniteSets, Integers

(* This second version of capcard_test.tla is less general
 * but easier to prove through CVC4's finite sets support *)

THEOREM ASSUME NEW a,
               NEW b,
               IsFiniteSet(a),
               IsFiniteSet(b)
        PROVE Cardinality(a \cap b) = Cardinality(a) - Cardinality(a \ b)
    OBVIOUS

====
