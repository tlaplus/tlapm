-------------- MODULE higher_order_statement_test ------------------
EXTENDS Integers, TLAPS

NatInductiveDefConclusion(f, f0, Def(_,_)) ==
     f = [i \in Nat |-> IF i = 0 THEN f0 ELSE Def(f[i-1], i)]
NatInductiveDefHypothesis(f, f0, Def(_,_)) ==
   (f =  CHOOSE g : g = [i \in Nat |-> IF i = 0 THEN f0 ELSE Def(g[i-1], i)])

THEOREM NatInductiveDef ==
          ASSUME NEW Def(_,_)
          PROVE  \A f, f0 : NatInductiveDefHypothesis(f, f0, Def)
                             => NatInductiveDefConclusion(f, f0, Def)
PROOF OMITTED

factorial[n \in Nat] == IF n = 0 THEN 1 ELSE n * factorial[n-1]

THEOREM \A n \in Nat : factorial[n] = IF n = 0 THEN 1 ELSE n * factorial[n-1]
<1>DEFINE Def(v, n) == n * v
<1>1. NatInductiveDefHypothesis(factorial, 1, Def)
  BY DEF NatInductiveDefHypothesis, factorial
<1>2. NatInductiveDefConclusion(factorial, 1, Def)
  BY <1>1, NatInductiveDef, Isa
<1>2bis. NatInductiveDefConclusion(factorial, 1, Def)
  BY <1>1, NatInductiveDef, ZenonT(30)
<1>3. QED
  BY <1>2 DEF NatInductiveDefConclusion
=============================================================================
