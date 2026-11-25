---- MODULE issue342_isa_bounded_choose_test ----

\* Isabelle must receive a bounded CHOOSE as its constant bChoose, so that
\* the library's lemma bChooseI applies (tlaplus/tlapm#342).

EXTENDS TLAPS

THEOREM ASSUME NEW P(_),
               NEW s,
               NEW a \in s,
               P(a)
        PROVE P(CHOOSE x \in s : P(x))
    BY IsaM("(rule bChooseI)")

\* A user identifier named bChoose must not collide with Isabelle's constant.
THEOREM ASSUME NEW P(_),
               NEW s,
               NEW bChoose \in s,
               P(bChoose)
        PROVE P(CHOOSE x \in s : P(x))
    BY IsaM("(rule bChooseI)")

====
