--------------------------- MODULE SimpleExampleWF_Max -----------------------
EXTENDS Naturals, TLAPS

Max(a, b) ==
  IF a > b THEN a ELSE b 

MaxProps == \A a, b \in Nat:
              /\ Max(a, b) >= a
              /\ Max(a, b) >= b
              /\ Max(a, b) \in Nat
              /\ Max(a, b) \in {a, b}
THEOREM MaxIsGEQ == MaxProps
  BY DEF MaxProps, Max

-----------------------------------------------------------------------------

---------- MODULE MaxAsFSM ---------------
EXTENDS Naturals
CONSTANTS a, b
ASSUME Assms == a \in Nat /\ b \in Nat
VARIABLES x
Null == CHOOSE n : n \notin Nat
Init == x = Null
Next ==
 /\ x = Null
 /\ \/ a >  b /\ x' = a
    \/ a =< b /\ x' = b
Live == WF_x(Next)
Spec == Init /\ [][Next]_x /\ Live
TypeOK == x \in Nat \cup {Null}
==========================================
CONSTANTS mA, mB
VARIABLE mX
ASSUME mAssms == mA \in Nat /\ mB \in Nat
m == INSTANCE MaxAsFSM WITH
  a <- mA,
  b <- mB,
  x <- mX

mIsMax == mX = Max(mA, mB)

(*
Type correctness.
*)
LEMMA mSpecTypeOK == m!Spec => []m!TypeOK
  <1>1. m!Init => m!TypeOK
        BY DEF m!Init, m!TypeOK
  <1>2. m!TypeOK /\ [m!Next]_mX => m!TypeOK'
        BY m!Assms DEF m!TypeOK, m!Next
  <1>q. QED BY <1>1, <1>2, PTL DEF m!Spec

(*
Invariant: mIsMax is stable.
*)
LEMMA mSpecStableMax == m!Spec => [](mIsMax => []mIsMax)
  <1>1. m!Init /\ mIsMax => mIsMax
        OBVIOUS
  <1>2. mIsMax /\ [m!Next]_mX => mIsMax'
        BY m!Assms DEF Max, mIsMax, m!Next
  <1>q. QED BY <1>1, <1>2, PTL DEF m!Spec

(*
Invariant: Either X = Null XOR X = Max(A, B)
*)
mXInv ==
  /\ (mX = m!Null) # mIsMax
  /\ (mX = m!Null) \in BOOLEAN
  /\ mIsMax \in BOOLEAN
LEMMA mSpecXInv == m!Spec => []mXInv
  <1>0. (mX # m!Null) \in BOOLEAN OBVIOUS
  <1>x. mIsMax \in BOOLEAN BY DEF mIsMax
  <1>1. m!Init => mXInv
        <2>0. SUFFICES ASSUME m!Init PROVE mXInv OBVIOUS
        <2>1. mX = m!Null BY <2>0 DEF m!Init
        <2>2. ~mIsMax
              BY <2>1, m!Assms, NoSetContainsEverything, MaxIsGEQ
              DEF mIsMax, MaxProps, m!Null  
        <2>q. QED BY <2>1, <2>2, <1>0, <1>x DEF mXInv
  <1>2. mXInv /\ [m!Next]_mX => mXInv'
        <2>1. SUFFICES ASSUME mXInv, m!Next PROVE mXInv'
              BY DEF m!Next, mXInv, mIsMax, Max
        <2>2. CASE mX = m!Null /\ ~mIsMax 
              BY <2>1, <2>2, m!Assms
              DEF mIsMax, Max, m!Next, mXInv
        <2>3. CASE mX # m!Null /\ mIsMax
              BY <2>1, <2>3, m!Assms
              DEF mIsMax, Max, m!Next, mXInv
        <2>4. QED BY <2>1, <2>2, <2>3, <1>0, <1>x, m!Assms DEF mXInv
  <1>q. QED BY <1>1, <1>2, PTL DEF m!Spec

(*
Prove the that MaxAsFSM produces the same results as Max eventually.
*)
LEMMA mSpecEventuallyMax == m!Spec => <>mIsMax
  <1>1. m!Spec => [](<>mIsMax \/ <><<m!Next>>_mX)
        <2> DEFINE P == mIsMax \/ ENABLED <<m!Next>>_mX
        <2> HIDE DEF P
        <2>1. m!Spec => []P
              <3>1. m!Init => P
                    <4>1. SUFFICES ASSUME m!Init PROVE P OBVIOUS
                    <4>2. SUFFICES ASSUME ~mIsMax PROVE ENABLED <<m!Next>>_mX
                          BY DEF P
                    <4>3. mX = m!Null BY <4>1 DEF m!Init
                    <4>4. mA \in Nat /\ mB \in Nat /\ m!Null \notin Nat
                          BY m!Assms, NoSetContainsEverything DEF m!Null
                    <4>5. SUFFICES ASSUME TRUE PROVE \E mX_1 : (
                            /\ mX = m!Null
                            /\ \/ mA >  mB /\ mX_1 = mA
                               \/ mA =< mB /\ mX_1 = mB
                          ) /\ ~mX_1 = mX
                          BY ExpandENABLED DEF m!Next
                    <4>6. CASE mA > mB
                          <5>1. WITNESS mA
                          <5>2. QED BY <5>1, <4>3, <4>4, <4>6
                    <4>7. CASE mA <= mB
                          <5>1. WITNESS mB
                          <5>2. QED BY <5>1, <4>3, <4>4, <4>7
                    <4>8. QED BY <4>6, <4>7, m!Assms
              <3>2. m!TypeOK /\ mXInv /\ P /\ [m!Next]_mX /\ mXInv' => P'
                    <4>1. SUFFICES ASSUME m!TypeOK,
                                          mXInv,
                                          P,
                                          mX = mX' \/ m!Next,
                                          mXInv'
                                   PROVE P'
                          OBVIOUS
                    <4>2. CASE mX = m!Null
                          <5>2. CASE mX = mX'
                                <6>0. mX' = m!Null BY <4>2, <5>2
                                <6>1. SUFFICES ASSUME TRUE PROVE (ENABLED <<m!Next>>_mX)'
                                      BY DEF P
                                <6>2. SUFFICES ASSUME TRUE PROVE \E mX_1 : (
                                        /\ mX' = m!Null
                                        /\ \/ mA > mB /\ mX_1 = mA
                                           \/ mA =< mB /\ mX_1 = mB
                                        ) /\ ~mX_1 = mX'
                                      BY <6>2, ExpandENABLED DEF m!Next
                                <6>3. mA' \in Nat /\ mB \in Nat /\ m!Null \notin Nat
                                      BY m!Assms, NoSetContainsEverything DEF m!Null
                                <6>a. CASE mA > mB
                                      <7>1. WITNESS mA
                                      <7>2. QED BY <7>1, <6>0, <6>a, <6>3
                                <6>b. CASE mA <= mB
                                      <7>1. WITNESS mB
                                      <7>2. QED BY <7>1, <6>0, <6>b, <6>3
                                <6>q. QED  BY <6>a, <6>b, m!Assms
                          <5>3. CASE mX # mX'
                                <6>1. mX' # m!Null BY <4>2, <5>3
                                <6>2. QED BY <6>1, <4>1, <4>2 DEF P, mIsMax, mXInv
                          <5>q. QED BY <5>2, <5>3
                    <4>3. CASE mIsMax
                          <5>1. mX # m!Null BY <4>1, <4>3 DEF mXInv
                          <5>2. ~m!Next BY <5>1 DEF m!Next 
                          <5>3. mX = mX' BY <5>2, <4>1
                          <5>4. mIsMax' BY <5>3, <4>3 DEF mIsMax 
                          <5>q. QED BY <5>4 DEF P
                    <4>q. QED BY <4>1, <4>2, <4>3 DEF mXInv
              <3>q. QED BY <3>1, <3>2, PTL, mSpecXInv, mSpecTypeOK DEF m!Spec
        <2>2. m!Spec => [](WF_mX(m!Next) => (<>mIsMax \/ <><<m!Next>>_mX))
              BY <2>1, PTL, mSpecTypeOK DEF P, m!Spec, m!Live
        <2>3. QED BY <2>1, <2>2, PTL DEF m!Spec, m!Live
  <1>2. ASSUME m!TypeOK, ~mIsMax, <<m!Next>>_mX PROVE mIsMax'
        BY <1>2, m!Assms
        DEF  mIsMax, Max, m!Next, m!TypeOK, m!Null
  <1>3. QED BY <1>1, <1>2, PTL, mSpecTypeOK

THEOREM mSpecIsMaxAsProp == m!Spec => <>[]mIsMax
  BY mSpecEventuallyMax, mSpecStableMax, PTL
  
=============================================================================
