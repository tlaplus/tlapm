-------------- MODULE Cantor8 --------------

Range (f) == { f[x] : x \in DOMAIN f }

Surj (f, S) == S \subseteq Range (f)

THEOREM Cantor ==
  \A S : ~ \E f \in [S -> SUBSET S] : Surj (f, SUBSET S)
PROOF
  <1>1. ASSUME NEW S,
               \E f \in [S -> SUBSET S] : Surj (f, SUBSET S)
        PROVE FALSE
        <2>. PICK f \in [S -> SUBSET S] : Surj (f, SUBSET S)
              BY <1>1
        <2>2. ~ Surj (f, SUBSET S)
              <3>1. DEFINE D == {x \in S : x \notin f[x]}
              <3>2. D \in SUBSET S
                    OBVIOUS
              <3>3. D \notin Range (f)
                    BY DEF Range
              <3>4. QED BY <3>2, <3>3 DEF Surj
        <2>3. QED BY <2>2
  <1>2. QED BY <1>1

====
