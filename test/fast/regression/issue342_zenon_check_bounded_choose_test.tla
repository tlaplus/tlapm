---- MODULE issue342_zenon_check_bounded_choose_test ----

\* Zenon's proof of a bounded CHOOSE, checked by Isabelle (-C), must name
\* Isabelle's constant bChoose (tlaplus/tlapm#342).

EXTENDS TLAPS

THEOREM ASSUME NEW P(_),
               NEW s,
               NEW a \in s,
               P(a)
        PROVE P(CHOOSE x \in s : P(x))
    BY Zenon

====
command: ${TLAPM} --toolbox 0 0 --nofp -C ${FILE}
nostderr: rejected
nostd*: status:failed
nostd*: ending abnormally
