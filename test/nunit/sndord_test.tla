---- MODULE sndord_test ----

EXTENDS TLAPS

(** Usable theorems quantify on fst-order operators.  This may become a problem
    for encodings into a fst-order logic like SMT-LIB.  This test exploits a
    flaw in the current SMT encoding that relies on the treatment of fst-order
    and snd-order operators.
*)

G(F(_), x) == F(x)

THEOREM Thm ==
        ASSUME NEW F(_),
               NEW a
        PROVE G(F, a) = F(a)
    (*BY DEF G*)

THEOREM Cor ==
        ASSUME NEW F1(_),
               NEW F2(_),
               NEW a
        PROVE G(F1, a) = G(F2, a)
    BY Thm

Z(x) == 0
S(x) == 1

THEOREM 0 = 1
<1>1 G(Z, 0) = 0    (*BY DEF G, Z*)
<1>2 G(S, 0) = 1    (*BY DEF G, S*)
<1> QED             (*BY ONLY Cor, <1>1, <1>2*)

====
