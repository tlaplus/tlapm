---- MODULE sndord_bis_test ----

EXTENDS TLAPS

(** A simpler variant of sndord_test *)

C == {}

G(F(_)) == F(C)

THEOREM Thm ==
        ASSUME NEW F(_)
        PROVE G(F) = F(C)
    (*BY DEF G*)

THEOREM Cor ==
        ASSUME NEW F1(_),
               NEW F2(_)
        PROVE G(F1) = G(F2)
    BY Thm

Z(x) == 0
S(x) == 1

THEOREM 0 = 1
<1>1 G(Z) = 0   (*BY DEF G, Z*)
<1>2 G(S) = 1   (*BY DEF G, S*)
<1> QED         (*BY ONLY Cor, <1>1, <1>2*)

====
stderr: status:failed
