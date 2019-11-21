--------------------------- MODULE select_bug_test ----------------------------
EXTENDS Naturals, TLAPS

LEMMA
  ASSUME NEW CONSTANT Def(_, _), NEW CONSTANT P(_),
         P(0),
         \A n \in Nat : P(n)  =>  P(n  +  1),
         ASSUME NEW CONSTANT P_1(_),
                P_1(0),
                \A n \in Nat : P_1(n)  =>  P_1(n  +  1)
         PROVE  \A n \in Nat : P_1(n)
  PROVE  \A n \in Nat : P(n)
PROOF OMITTED

THEOREM FiniteNatInductiveDef ==
  ASSUME NEW Def(_,_)
  PROVE  \A n \in Nat: \A f, f0 :
              (f =  CHOOSE g : g = [i \in 0..n |-> IF i = 0
                                                   THEN f0
                                                   ELSE Def(g[i-1], i)])
              => /\ f = [i \in 0..n |-> IF i = 0 THEN f0
                                                 ELSE Def(f[i-1], i)]
                 /\ \A h : (h = [i \in 0..n |-> IF i = 0 THEN f0
                                                         ELSE Def(h[i-1], i)])
                           => (h = f)
PROOF OMITTED

LEMMA
  ASSUME NEW Def(_,_)
  PROVE  /\ TRUE
         /\ \A n \in Nat: \A f, f0 :
              (f =  CHOOSE g : g = [i \in 0..n |-> IF i = 0
                                                   THEN f0
                                                   ELSE Def(g[i-1], i)])
              => /\ f = [i \in 0..n |-> IF i = 0 THEN f0
                                                 ELSE Def(f[i-1], i)]
                 /\ \A h : (h = [i \in 0..n |-> IF i = 0 THEN f0
                                                         ELSE Def(h[i-1], i)])
                           => (h = f)
BY FiniteNatInductiveDef


=============================================================================
nostd*: ending abnormally
