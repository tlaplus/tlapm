---- MODULE test_obl_expand ----
EXTENDS FiniteSetTheorems
THEOREM FALSE
    <1>1. TRUE OBVIOUS
    <1>2. TRUE
    <1>3. TRUE
    <1>q. QED BY <1>1, <1>2, <1>3
THEOREM FALSE
    <1>q. QED
       <2>1. TRUE
       <2>q. QED BY <2>1
  ----- MODULE sub ------
  VARIABLE X
  LEMMA X = X
  =======================
====
