-------------- MODULE Cantor9_test --------------

Range (f) == { f[x] : x \in DOMAIN f }

Surj (f, S) == S \subseteq Range (f)

THEOREM Cantor ==
  ~ \E f : Surj (f, SUBSET (DOMAIN f))
<1>1. SUFFICES ASSUME \E f : Surj (f, SUBSET (DOMAIN f))
               PROVE  FALSE
  OBVIOUS
<1>. PICK f : Surj (f, SUBSET (DOMAIN f))
  BY <1>1!1!1
<1>3. ~ Surj (f, SUBSET (DOMAIN f))
  <2>1. DEFINE D == {x \in DOMAIN f : x \notin f[x]}
  <2>2. D \in SUBSET (DOMAIN f) OBVIOUS
  <2>3. D \notin Range (f) BY DEF Range
  <2>4. QED BY <2>2, <2>3 DEF Surj
<1>4. QED BY <1>3

====
