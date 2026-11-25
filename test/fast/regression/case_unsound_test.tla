---- MODULE case_unsound_test ----

\* Soundness controls for CASE (tlaplus/tlapm#304).  A CASE denotes
\* CHOOSE'n among the results of its enabled arms; arms are unordered.
\* Every obligation below is invalid and must not be proved.  Lowering
\* CASE to an ordered IF/ite proves some of them.  The Isabelle timeouts
\* bound the cost of the expected failures.

EXTENDS Naturals, TLAPS

\* Swapping two enabled arms leaves the set of enabled results unchanged.
THEOREM SmtSwap ==
  (CASE TRUE -> "u" [] TRUE -> "v" [] OTHER -> "w")
    # (CASE TRUE -> "v" [] TRUE -> "u" [] OTHER -> "w")
BY SMT

THEOREM ZenonSwap ==
  (CASE TRUE -> "u" [] TRUE -> "v" [] OTHER -> "w")
    # (CASE TRUE -> "v" [] TRUE -> "u" [] OTHER -> "w")
BY Zenon

THEOREM IsaSwap ==
  (CASE TRUE -> "u" [] TRUE -> "v" [] OTHER -> "w")
    # (CASE TRUE -> "v" [] TRUE -> "u" [] OTHER -> "w")
BY IsaT(2)

THEOREM SmtSwapNoOther ==
  (CASE TRUE -> "u" [] TRUE -> "v") # (CASE TRUE -> "v" [] TRUE -> "u")
BY SMT

THEOREM ZenonSwapNoOther ==
  (CASE TRUE -> "u" [] TRUE -> "v") # (CASE TRUE -> "v" [] TRUE -> "u")
BY Zenon

THEOREM IsaSwapNoOther ==
  (CASE TRUE -> "u" [] TRUE -> "v") # (CASE TRUE -> "v" [] TRUE -> "u")
BY IsaT(2)

THEOREM SmtSwapSymbolic ==
  ASSUME NEW p, NEW q, p, q
  PROVE  (CASE p -> "u" [] q -> "v" [] OTHER -> "w")
            # (CASE q -> "v" [] p -> "u" [] OTHER -> "w")
BY SMT

THEOREM ZenonSwapSymbolic ==
  ASSUME NEW p, NEW q, p, q
  PROVE  (CASE p -> "u" [] q -> "v" [] OTHER -> "w")
            # (CASE q -> "v" [] p -> "u" [] OTHER -> "w")
BY Zenon

THEOREM IsaSwapSymbolic ==
  ASSUME NEW p, NEW q, p, q
  PROVE  (CASE p -> "u" [] q -> "v" [] OTHER -> "w")
            # (CASE q -> "v" [] p -> "u" [] OTHER -> "w")
BY IsaT(2)

\* Neither the first nor the last enabled arm has priority.
THEOREM SmtFirstArm == (CASE TRUE -> "u" [] TRUE -> "v") = "u"
BY SMT

THEOREM ZenonFirstArm == (CASE TRUE -> "u" [] TRUE -> "v") = "u"
BY Zenon

THEOREM IsaFirstArm == (CASE TRUE -> "u" [] TRUE -> "v") = "u"
BY IsaT(2)

THEOREM SmtLastArm == (CASE TRUE -> "u" [] TRUE -> "v") = "v"
BY SMT

THEOREM ZenonLastArm == (CASE TRUE -> "u" [] TRUE -> "v") = "v"
BY Zenon

THEOREM IsaLastArm == (CASE TRUE -> "u" [] TRUE -> "v") = "v"
BY IsaT(2)

\* Likewise for a CASE in a hypothesis and in an expanded definition.
THEOREM SmtHyp ==
  ASSUME NEW r, r = (CASE TRUE -> "u" [] TRUE -> "v")
  PROVE  r = "u"
BY SMT

THEOREM ZenonHyp ==
  ASSUME NEW r, r = (CASE TRUE -> "u" [] TRUE -> "v")
  PROVE  r = "u"
BY Zenon

THEOREM IsaHyp ==
  ASSUME NEW r, r = (CASE TRUE -> "u" [] TRUE -> "v")
  PROVE  r = "u"
BY IsaT(2)

Op == CASE TRUE -> "u" [] TRUE -> "v"

THEOREM SmtDef == Op = "u"
BY SMT DEF Op

THEOREM ZenonDef == Op = "u"
BY Zenon DEF Op

THEOREM IsaDef == Op = "u"
BY IsaT(2) DEF Op

\* CASEs with the same set of enabled results are equal, whatever their
\* number of arms: here the third arm repeats the first.
THEOREM SmtArity ==
  ASSUME NEW p, NEW q
  PROVE  (CASE p -> "u" [] q -> "v") # (CASE p -> "u" [] q -> "v" [] p -> "u")
BY SMT

THEOREM ZenonArity ==
  ASSUME NEW p, NEW q
  PROVE  (CASE p -> "u" [] q -> "v") # (CASE p -> "u" [] q -> "v" [] p -> "u")
BY Zenon

THEOREM IsaArity ==
  ASSUME NEW p, NEW q
  PROVE  (CASE p -> "u" [] q -> "v") # (CASE p -> "u" [] q -> "v" [] p -> "u")
BY IsaT(2)

THEOREM SmtArityOverlap ==
  ASSUME NEW p, NEW q, p, q
  PROVE  (CASE p -> "u" [] q -> "v") # (CASE p -> "u" [] q -> "v" [] p -> "u")
BY SMT

THEOREM ZenonArityOverlap ==
  ASSUME NEW p, NEW q, p, q
  PROVE  (CASE p -> "u" [] q -> "v") # (CASE p -> "u" [] q -> "v" [] p -> "u")
BY Zenon

THEOREM IsaArityOverlap ==
  ASSUME NEW p, NEW q, p, q
  PROVE  (CASE p -> "u" [] q -> "v") # (CASE p -> "u" [] q -> "v" [] p -> "u")
BY IsaT(2)

\* Boolean-valued and action-level CASE, from
\* https://github.com/tlaplus/rfcs/issues/26#issuecomment-4562790168.
VARIABLE x

Init == x = 0
InvCase == CASE x \in Nat -> FALSE [] x \in Nat -> TRUE
Next == CASE x \in Nat -> x' = 1 [] x \in Nat -> x' = 2
Inv == x \in Nat /\ x <= 1

THEOREM SmtBool == Init => (InvCase = FALSE)
BY SMT DEF Init, InvCase

THEOREM ZenonBool == Init => (InvCase = FALSE)
BY Zenon DEF Init, InvCase

THEOREM IsaBool == Init => (InvCase = FALSE)
BY IsaT(2) DEF Init, InvCase

THEOREM SmtBoolFormula == Init => ~InvCase
BY SMT DEF Init, InvCase

THEOREM ZenonBoolFormula == Init => ~InvCase
BY Zenon DEF Init, InvCase

THEOREM IsaBoolFormula == Init => ~InvCase
BY IsaT(2) DEF Init, InvCase

THEOREM SmtAction == Inv /\ [Next]_x => Inv'
BY SMT DEF Inv, Next

THEOREM ZenonAction == Inv /\ [Next]_x => Inv'
BY Zenon DEF Inv, Next

THEOREM IsaAction == Inv /\ [Next]_x => Inv'
BY IsaT(2) DEF Inv, Next

====
nostd*: ending abnormally
stderr: 36/72 obligations failed
