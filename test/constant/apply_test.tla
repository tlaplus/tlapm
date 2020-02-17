---- MODULE apply_test ----

EXTENDS TLAPS

Apply(F(_), x) == F(x)

THEOREM ASSUME NEW F(_),
               NEW x
        PROVE F(Apply(F, x)) = Apply(F, F(x))
<1>1 F(Apply(F, x)) = F(F(x))           BY DEF Apply
<1>2              @ = Apply(F, F(x))    BY DEF Apply
<1> QED                                 BY ONLY <1>1, <1>2

====
