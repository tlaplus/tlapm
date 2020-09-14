---- MODULE quant_pred_test ----

EXTENDS TLAPS

(* The following second-order theorem is difficult if
   Q is encoded as a predicate but the quantified P in
   the lemma is not encoded as a predicate.
*)
C == {}
Q(x) == x # C
THEOREM ASSUME ASSUME NEW P(_)
               PROVE \A x : P(x)
        PROVE FALSE
<1>1 \A x : Q(x) <=> x # C
    (*BY DEF Q*)
<1> QED
    BY <1>1

====

