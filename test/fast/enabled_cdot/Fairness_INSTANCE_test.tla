---- MODULE Fairness_INSTANCE_test ----
EXTENDS Integers, TLAPS

---- MODULE Inner ----
EXTENDS Integers
VARIABLES x, y

Next == x' = x + 1 /\ y' = y - 1
vars == <<x, y>>
En == ENABLED <<Next>>_vars
WFair == WF_vars(Next)
SFair == SF_vars(Next)
======================

VARIABLES u, v, z

TypeOK == z \in Int

\* Instantiated WF/SF unfolds to the instantiated ENABLED (I!En, J!En), so
\* PTL can relate it to the definitions.  See test/soundness_tests/issue69_*
\* for the soundness tests (https://github.com/tlaplus/tlapm/issues/69).

\* Under the non-injective substitution x <- z, y <- z, I!En holds when
\* z \in Int, but the instantiated step <<I!Next>>_(I!vars) is impossible.
\* Hence []TypeOK /\ I!WFair and []TypeOK /\ I!SFair are both inconsistent.
I == INSTANCE Inner WITH x <- z, y <- z

LEMMA IEnHolds == TypeOK => I!En
BY ExpandENABLED DEF TypeOK, I!En

LEMMA StepImpossible == TypeOK => ~ <<I!Next>>_(I!vars)
BY DEF TypeOK, I!Next, I!vars

THEOREM InstantiatedWFairDef ==
  I!WFair <=> (<>[]I!En => []<><<I!Next>>_(I!vars))
BY PTL DEF I!WFair, I!En

THEOREM InstantiatedSFairDef ==
  I!SFair <=> ([]<>I!En => []<><<I!Next>>_(I!vars))
BY PTL DEF I!SFair, I!En

THEOREM InstantiatedWFairFalse == []TypeOK /\ I!WFair => FALSE
BY IEnHolds, StepImpossible, InstantiatedWFairDef, PTL

THEOREM InstantiatedSFairFalse == []TypeOK /\ I!SFair => FALSE
BY IEnHolds, StepImpossible, InstantiatedSFairDef, PTL

\* Under the injective renaming x <- u, y <- v, instantiated fairness is
\* equivalent to fairness of the instantiated action.
J == INSTANCE Inner WITH x <- u, y <- v

LEMMA JEnEquiv == J!En <=> ENABLED <<J!Next>>_(J!vars)
BY ExpandENABLED DEF J!En, J!Next, J!vars

THEOREM InjectiveWFair == J!WFair <=> WF_(J!vars)(J!Next)
<1>1. J!WFair <=> (<>[]J!En => []<><<J!Next>>_(J!vars))
  BY PTL DEF J!WFair, J!En
<1>. QED
  BY <1>1, JEnEquiv, PTL

THEOREM InjectiveSFair == J!SFair <=> SF_(J!vars)(J!Next)
<1>1. J!SFair <=> ([]<>J!En => []<><<J!Next>>_(J!vars))
  BY PTL DEF J!SFair, J!En
<1>. QED
  BY <1>1, JEnEquiv, PTL

=======================================
