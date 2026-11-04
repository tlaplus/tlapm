--------------------------- MODULE BoundedBuffer ---------------------------
EXTENDS Integers, Sequences, TLAPS

CONSTANT Msg, N

ASSUME NAssump == N \in Nat \ {0}
USE NAssump

BufCtr == 0..(2*N-1)

a (+) b == (a + b) % 2*N
a (-) b == (a - b) % 2*N
----------------------------------------------------------------------------
VARIABLE buf, p, c

vars == <<buf, p, c>>

TypeOK == /\ buf \in [0..N-1 -> Msg]
          /\ p \in BufCtr
          /\ c \in BufCtr

Init == /\ buf \in [0..N-1 -> Msg]
        /\ p = 0
        /\ c = 0

Put == /\ p (-) c # N
       /\ \E v \in Msg : buf' = [buf EXCEPT ![p % N] = v]
       /\ p' = p (+) 1
       /\ c' = c

Get == /\ p # c
       \* Consume element in buf[c mod N]
       /\ c' = c (+) 1
       /\ UNCHANGED <<p, buf>>

Next == Put \/ Get

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------

PCInv == p (-) c \in 0..N

Inv == TypeOK /\ PCInv

----------------------------------------------------------------------------

LEMMA OPlusDef == \A a, b \in BufCtr :
                     a (+) b = IF a + b < 2*N THEN a + b
                                              ELSE a + b - 2*N
BY DEF (+), BufCtr

LEMMA OMinusDef == \A a, b \in BufCtr :
                     a (-) b = IF a - b >= 0 THEN a - b
                                             ELSE a - b + 2*N
BY DEF (-), BufCtr

LEMMA ModRules == \A a, b \in BufCtr :
                     /\ (a (+) 1) (-) b = (a (-) b) (+) 1
                     /\ a (-) (b (+) 1) = (a (-) b) (-) 1
BY OPlusDef, OMinusDef DEF BufCtr

THEOREM Invariant == Spec => []Inv
<1>. USE NAssump DEF Inv, PCInv, TypeOK, BufCtr
<1>1. Init => Inv
  BY OMinusDef DEF Init
<1>2. Inv /\ [Next]_vars => Inv'
  <2>. SUFFICES ASSUME Inv, Next PROVE Inv'
    BY DEF vars 
  <2>1. CASE Put 
    <3>1. TypeOK'
      BY <2>1 DEF Put, (+), (-)
    <3>2. p (-) c \in 0 .. N-1 
      BY <2>1 DEF Put
    <3>3. p' (-) c' = (p (-) c) + 1
      BY <2>1, <3>2 DEF Put, (+), (-)
    <3>. QED  BY <3>1, <3>2, <3>3
  <2>2. CASE Get 
    <3>1. TypeOK'
      BY <2>2 DEF Get, (+), (-)
    <3>2. p (-) c \in 1 .. N 
      BY <2>2 DEF Get, (-)
    <3>3. p' (-) c' = (p (-) c) (-) 1
      BY <2>2, <3>2, ModRules DEF Get 
    <3>4. @ = (p (-) c) - 1
      BY <3>2 DEF (-)
    <3>. QED  BY <3>1, <3>2, <3>3, <3>4
  <2>. QED  BY <2>1, <2>2 DEF Next 
<1>3. QED  BY <1>1, <1>2, PTL DEF Spec 

------------------------------------------------------------------------------ 
(****************************************************************************)
(* Proof of refinement.                                                     *)
(****************************************************************************)

chBar == [i \in 1..(p (-) c) |-> buf[(c + i - 1) % N]]
C == INSTANCE PCalBoundedChannel WITH ch <- chBar

LEMMA chBarType == Inv => /\ chBar \in Seq(Msg)
                          /\ Len(chBar) \in 0..N
BY DEF Inv, BufCtr, TypeOK, PCInv, chBar

THEOREM Refinement == Spec => C!Spec 
<1>1. Init => C!Init 
  BY DEF Init, C!Init, chBar, (-)
<1>2. Inv /\ [Next]_vars => [C!Next]_<< chBar >>
  <2>. SUFFICES ASSUME Inv, [Next]_vars PROVE [C!Next]_<< chBar >>
    OBVIOUS 
  <2>. USE DEF Inv, TypeOK, PCInv, chBar, BufCtr
  <2>1. CASE Put 
    <3>1. PICK v \in Msg :
            /\ p (-) c # N
            /\ buf' = [buf EXCEPT ![p % N] = v]
            /\ p' = p (+) 1
            /\ c' = c
      BY <2>1 DEF Put 
    <3>2. p (-) c \in 0 .. N-1 
      BY <3>1
    <3>3. p' (-) c' = (p (-) c) + 1
      BY <3>1, <3>2 DEF (+), (-)
    <3>4. Append(chBar, v) =
           [i \in 1..((p(-)c)+1) |->
             IF i = (p(-)c)+1 THEN v ELSE chBar[i]]
      BY chBarType
    <3>5. p % N = (c + (((p(-)c)+1) - 1)) % N
      BY <3>2, OMinusDef
    <3>6. ASSUME NEW i \in 1..((p(-)c)+1)
          PROVE  /\ (c + (i - 1)) % N \in 0..(N-1)
                 /\ (i = (p(-)c)+1) <=> ((c + (i - 1)) % N = p % N)
      BY <3>2, OMinusDef
    <3>7. chBar' = Append(chBar, v)
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6
    <3>. QED  BY <3>2, <3>7 DEF C!Send, C!Next
  <2>2. CASE Get 
    <3>1. /\ p # c 
          /\ c' = c (+) 1
          /\ UNCHANGED <<p, buf>> 
      BY <2>2 DEF Get 
    <3>. DEFINE pmc == p (-) c
    <3>2. pmc \in 1 .. N 
      BY <3>1, OMinusDef
    <3>3. pmc' = pmc (-) 1
      BY <3>1, ModRules 
    <3>4. @ = pmc - 1
      BY <3>2, OMinusDef
    <3>5. Tail(chBar) = [i \in 1..(pmc-1) |-> buf[(c + i) % N]]
      BY chBarType, <3>2
    <3>6. \A i \in 1..(pmc-1) : (c' + i - 1) % N = (c + i) % N
      BY <3>1, <3>2, OPlusDef
    <3>7. chBar' = Tail(chBar)
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6
    <3>. QED  BY <3>2, <3>7 DEF C!Rcv, C!Next 
  <2>3. CASE UNCHANGED vars 
    BY <2>3 DEF vars 
  <2>. QED  BY <2>1, <2>2, <2>3 DEF Next
<1>. QED  BY <1>1, <1>2, Invariant, PTL DEF Spec, C!Spec, C!vars 

=============================================================================
