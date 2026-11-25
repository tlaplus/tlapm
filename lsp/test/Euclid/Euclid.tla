---- MODULE Euclid ----
EXTENDS Integers, GCD
CONSTANTS M, N
ASSUME MNPosInt ==
  /\ M \in Nat \ {0}
  /\ N \in Nat \ {0}

VARIABLES x, y
vars == <<x, y>>

NextX == x > y /\ x' = x - y /\ UNCHANGED y
NextY == x < y /\ y' = y - x /\ UNCHANGED x
Next == NextX \/ NextY
Init == x = M /\ y = N

Spec == Init /\ [][Next]_vars

--------------------------------------

PartialCorrectness == x = y => x = GCD(M, N)

TypeOK ==
  /\ x \in Nat \ {0}
  /\ y \in Nat \ {0}

IInv == GCD(x, y) = GCD(M, N)

--------------------------------------

INSTANCE TLAPS

THEOREM GCD1 == \A m \in Nat \ {0} : GCD(m, m) = m
  <1> USE MNPosInt
  <1> TAKE m \in Nat \ {0}
  <1>0. m \in Nat OBVIOUS
  <1>1. Divides(m, m) BY DEF Divides
  <1>2. \A i \in Nat : Divides(i, m) => (i <= m) BY DEF Divides
  <1> QED BY <1>0, <1>1, <1>2 DEFS GCD, SetMax, DivisorsOf

THEOREM GCD2 == \A m, n \in Nat \ {0} : GCD(m, n) = GCD(n, m)
  BY DEFS GCD, SetMax, DivisorsOf, Divides

THEOREM GCD3 == \A m, n \in Nat \ {0} : (n > m) => GCD(m, n) = GCD(m, n - m)
  <1> USE MNPosInt
  <1> TAKE m, n \in Nat \ {0}
  <1> HAVE n > m
  <1>2. \A i \in Nat : Divides(i, m) /\ Divides(i, n) <=> Divides(i, m) /\ Divides(i, n - m)
    <2> TAKE i \in Nat
    <2> m \in Nat /\ n \in Nat OBVIOUS
    <2>1. Divides(i, m) /\ Divides(i, n) => Divides(i, m) /\ Divides(i, n - m)
      <3> HAVE (\E q \in Nat : m = q * i) /\ (\E q \in Nat : n = q * i)
      <3> PICK qm \in Nat : m = qm * i OBVIOUS (* TODO: Crash here. Several obligations. One of them is omitted. *)
      <3> PICK qn \in Nat : n = qn * i OBVIOUS (* TODO: Crash here. Several obligations. One of them is omitted. *)
      <3>1. \E q \in Nat : m = q * i BY DEF Divides
      <3>2. \E q \in Nat : n - m = q * i
        <4> q == qn - qm
        <4> HIDE DEF q
        <4>1. q \in Nat BY DEF q
        <4>2. USE DEF Divides
        <4> WITNESS q \in Nat
        <4> QED BY DEFS Divides, q
      <3> QED BY <3>1, <3>2 DEF Divides
    <2>2. Divides(i, m) /\ Divides(i, n - m) => Divides(i, m) /\ Divides(i, n)
      <3>1. HAVE (\E q \in Nat : m = q * i) /\ (\E q \in Nat : n - m = q * i)
      <3>2. \E q \in Nat : m = q * i BY <3>1 DEF Divides
      <3>3. \E q \in Nat : n = q * i
        <4> PICK qm \in Nat : m = qm * i BY <3>1
        <4> PICK qd \in Nat : n - m = qd * i BY <3>1
        <4> q == qm + qd
        <4> HIDE DEF q
        <4>1. q \in Nat BY DEF q
        <4>2. USE <3>1 DEF Divides
        <4> WITNESS q \in Nat
        <4> QED BY <3>1 DEF q, Divides
      <3> QED BY <3>2, <3>3 DEF Divides
    <2> QED BY <2>1, <2>2
  <1> QED BY <1>2 DEFS GCD, DivisorsOf, SetMax


THEOREM SpecTypeOK == Spec => []TypeOK
  <1> USE MNPosInt
  <1>1. Init => TypeOK BY DEFS Init, TypeOK
  <1>2. TypeOK /\ [Next]_vars => TypeOK' BY DEFS TypeOK, Next, vars, NextX, NextY
  <1>q. QED BY <1>1, <1>2, PTL DEF Spec

THEOREM Spec => []PartialCorrectness
  <1> USE GCD1, GCD2, GCD3
  <1>1. Init => IInv
    <2>1. HAVE Init
    <2>q. QED BY <2>1, MNPosInt DEFS IInv, Init, TypeOK
  <1>2. TypeOK /\ IInv /\ [Next]_vars => IInv'
    <2>1. HAVE TypeOK /\ IInv /\ [Next]_vars
    <2>2. TypeOK BY <2>1
    <2>3. IInv BY <2>1
    <2>4. [Next]_vars BY <2>1
    <2>5. CASE Next
      <3>1. CASE NextX BY <2>1, <3>1 DEFS NextX, IInv, TypeOK
      <3>2. CASE NextY BY <2>1, <3>2 DEFS NextY, IInv, TypeOK
      <3> QED BY <2>5, <3>1, <3>2 DEF Next
    <2>6. CASE UNCHANGED vars BY <2>3, <2>6 DEFS IInv, vars, GCD, TypeOK, SetMax, DivisorsOf
    <2> QED BY <2>4, <2>5, <2>6
  <1>3. TypeOK /\ IInv => PartialCorrectness BY DEFS IInv, PartialCorrectness, TypeOK
  <1>q. QED BY <1>1, <1>2, <1>3, SpecTypeOK, PTL DEF Spec

====
