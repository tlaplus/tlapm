--------------------------- MODULE BoundedBuffer ---------------------------
EXTENDS Integers, Sequences, TLAPS

CONSTANT Msg, N

ASSUME NAssump == N \in Nat \ {0}

BufCtr == 0..(2*N-1)

a (+) b == (a + b) % 2*N
a (-) b == (a - b) % 2*N
----------------------------------------------------------------------------
VARIABLE buf, p, c

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

Spec == Init /\ [][Next]_<<buf, p, c>>

----------------------------------------------------------------------------

chBar == [i \in 1..(p (-) c) |-> buf[(c + i - 1) % N]]

C == INSTANCE PCalBoundedChannel WITH ch <- chBar

PosNat == Nat \ {0}

PCInv == p (-) c \in 0..N

Inv == TypeOK /\ PCInv

----------------------------------------------------------------------------

LEMMA ModDef == \A i \in Int, j \in Nat \ {0} :
                   /\ i % j \in 0..(j-1)
                   /\ i \in 0..(j-1) => i % j = i
                   /\ i % j = (i + j) % j
                   /\ i % j = (i - j) % j
  BY SMT

(***************************************************************************)
(* The following definition and assumed lemma are added because of a bug   *)
(* in SimpleArithmetic that does not allow it to deduce 2*N \in Int from   *)
(* NAssump even though it can deduce 2*N-1 \in Nat \ {0}.                  *)
(***************************************************************************)
K == 2*N

LEMMA OPlusDef == \A a, b \in BufCtr :
                     a (+) b = IF a + b < 2*N THEN a + b
                                              ELSE a + b - 2*N
  BY NAssump, SMT DEF (+), BufCtr

LEMMA KFacts == K \in Int /\ K > N 
  BY NAssump, SMT DEF K

LEMMA KBufCtr == BufCtr = 0..(K-1)
  BY SMT DEF K, BufCtr

LEMMA 1InBufCtr == 1 \in BufCtr
  BY NAssump, KFacts, KBufCtr, SMT
                                         
LEMMA OMinusDef == \A a, b \in BufCtr :
                     a (-) b = IF a - b >= 0 THEN a - b
                                             ELSE a - b + 2*N
  BY NAssump, SMT DEF K, (-), BufCtr

LEMMA ModRules == \A a, b \in BufCtr :
                     /\ (a (+) 1) (-) b = (a (-) b) (+) 1
                     /\ a (-) (b (+) 1) = (a (-) b) (-) 1
                                           
LEMMA ModN1 == \A a \in Int : a % N \in 0..(N-1)
  BY NAssump, SMT

LEMMA ModN2 == \A a \in 0..(N-1) : a % N = a
  BY NAssump, SMT

LEMMA ModN3 == \A a, b \in Int : 
                  /\ (a + b) % N = ((a % N) + (b % N)) % N
                  /\ (a - b) % N = ((a % N) - (b % N)) % N

LEMMA ModN4 == \A a \in Int : /\ a % N = (a + N) % N
                              /\ a % N = (a - N) % N
  BY NAssump, SMT

LEMMA Mod2N == \A i \in Int : (i % 2*N) % N = i % N
  BY NAssump, SMT

LEMMA PutGet == /\ Inv /\ Put => (p' (-) c') = (p (-) c) + 1
                /\ Inv /\ Get => /\ (p (-) c) # 0
                                 /\ (p' (-) c') = (p (-) c) - 1
<1>. USE NAssump, ModRules DEFS Inv, TypeOK, K, BufCtr
<1>1. PutGet!1
  BY KBufCtr, ModRules, KFacts, NAssump, 1InBufCtr, KBufCtr, OPlusDef, SMT 
  DEF K, Put, Inv, PCInv
<1>2. PutGet!2
  BY OMinusDef, Z3 DEF Get
<1>4. QED
  BY <1>1, <1>2

THEOREM Spec => []Inv
<1>. USE NAssump DEF Inv, PCInv, TypeOK, BufCtr
<1>1. Init => Inv
  BY OMinusDef, SMT DEF Init
<1>2. Inv /\ [Next]_<<buf, p, c>> => Inv'
  BY PutGet, OPlusDef, Z3
  DEF Next, Put, Get, K
<1>3. QED
  PROOF OMITTED

LEMMA SeqDef == \A S : 
                  \A n \in Nat :
                    \A f \in [1..n -> S] :
                       f \in Seq(S) /\ Len(f) = n
PROOF OMITTED

LEMMA EmptySeq == \A S : \A s \in Seq(S) : Len(s) = 0 <=> s = << >>
PROOF OMITTED

LEMMA AppendDef == \A S : 
                     \A s \in Seq(S) :
                       \A e : Append(s, e) = 
                                [i \in 1..(Len(s)+1) |-> 
                                   IF i = Len(s)+1 THEN e ELSE s[i]]
PROOF OMITTED

LEMMA TailDef == \A S : 
                   \A s \in Seq(S) :
                     (Len(s) # 0) => 
                        Tail(s) = [i \in 1..(Len(s)-1) |-> s[i+1]]
PROOF OMITTED

AXIOM LenAxiom == \A S :
                   \A seq \in Seq(S) :  /\ Len(seq) \in Nat
                                        /\ seq \in [1..Len(seq) -> S]

LEMMA chBarType == Inv => /\ chBar \in Seq(Msg)
                          /\ Len(chBar) \in 0..N
<1> SUFFICES ASSUME Inv PROVE chBarType!2 OBVIOUS       
<1> USE DEF Inv, PCInv
<1>1. p (-) c \in Nat
  BY NAssump, SMT
<1>2. chBar \in [1..(p (-) c) -> Msg]
  BY KFacts, NAssump, ModN1, KBufCtr, SMT DEF TypeOK, chBar
<1>3. QED
  BY <1>1, <1>2, SeqDef DEF chBar 
    
THEOREM Spec => C!Spec
<1>. USE NAssump DEFS K, BufCtr
<1>1. Init => C!Init
  BY OMinusDef, SeqDef, EmptySeq, SMT 
  DEF C!Init, chBar, Init, K, BufCtr
<1>2. Inv /\ Next => C!Next \/ UNCHANGED chBar
  <2> SUFFICES ASSUME Inv, Next
      PROVE    C!Next
    BY SMT
  <2>2. chBar \in [1..(p (-) c) -> Msg]
    BY ModN1, SMT DEF Inv, TypeOK, PCInv, chBar
  <2>3. /\ chBar \in Seq(Msg)
        /\ Len(chBar) = p (-) c
    <3>1. \A n \in Nat :
               \A f \in [1 .. n -> Msg] : f  \in  Seq(Msg)  /\  Len(f)  =  n
      BY SeqDef, Z3
    <3>2. p (-) c \in Nat
      BY SMT DEF Inv, PCInv
    <3>3. \A f \in [1 .. (p (-) c) -> Msg] : f  \in  Seq(Msg)  /\  Len(f)  =  p (-) c
      BY <3>1, <3>2
    <3>q. QED
      BY <2>2, <3>3
  <2>4. ASSUME Put
        PROVE  C!Send
    <3> USE Put
    <3>1. PICK v \in Msg : buf' = [buf EXCEPT ![p % N] = v]
      BY SMT DEF Put
    <3>2. SUFFICES chBar' = Append(chBar, v)
      BY <2>3, Z3 DEF Put, C!Send
    <3>3. Append(chBar, v) = 
           [i \in 1..((p(-)c)+1) |->
             IF i = (p(-)c)+1 THEN v ELSE chBar[i]]
      BY <2>3, AppendDef, Z3
    <3>4. /\ p % N = (c + (((p(-)c)+1) - 1)) % N
          /\ \A i \in 1..((p(-)c)+1) :
                /\ (c + (i - 1)) % N \in 0..(N-1)
                /\ (i = (p(-)c)+1) <=> ((c + (i - 1)) % N = p % N)
      <4>1. p (-) c \in 0..(N-1)
        BY SMT DEF Put, Inv, PCInv
      <4> DEFINE pmc == p (-) c
      <4>2. p % N = (c + ((pmc+1) - 1)) % N
        <5>1. /\ pmc \in Int
              /\ p \in Int
              /\ c \in Int
              /\ p-c \in Int
          BY SMT DEF Inv, PCInv, TypeOK
        <5> HIDE DEF pmc
        <5>3.  (c + ((pmc+1) - 1)) % N = (c + pmc) % N 
          BY <5>1, SMT 
        <5>4. @ = ((c % N) + (pmc % N)) % N
          BY ModN3, <5>1, Z3 
        <5>5. @ = ((c % N) + ((p-c) % N)) % N
          BY Mod2N, <5>1, SMT DEF pmc, (-)
        <5>8. QED
          BY <5>3, <5>4, ModN3, <5>5, Z3 DEF Inv, PCInv, TypeOK
      <4> SUFFICES ASSUME NEW i \in 1..(pmc+1)
                   PROVE  /\ (c + (i - 1)) % N \in 0..(N-1)
                          /\ ((c + (i - 1)) % N = p % N) => (i = pmc+1) 
        BY <4>2, Z3
      <4>3. (c + (i - 1)) % N \in 0..(N-1)
        BY <4>1, ModN1, SMT DEF  Inv, TypeOK
      <4>4. ASSUME i # pmc+1
            PROVE  (c + (i - 1)) % N # p % N
        <5>2. ASSUME NEW a \in Int, NEW b \in Int,  
                     a - b \in 0..(N-1),
                     a - b # 0
              PROVE  a % N # b % N
          BY <5>2, ModN3, SMT
        <5>3. QED
          BY <4>4, <5>2, <4>2, Z3 DEF Inv, TypeOK, PCInv, Put
      <4>5. QED
        BY <4>3, <4>4, SMT
    <3>5. chBar' = [i \in 1..((p (-) c) + 1) |-> 
                      IF (c + i - 1) % N = p % N THEN v 
                                                 ELSE buf[(c + i - 1) % N]]
      BY <3>1, <3>4, PutGet, SMT DEF Inv, TypeOK, chBar, Put
    <3>7. <3>3!2 = <3>5!2
      BY <3>4, Z3 DEF chBar, Inv, PCInv
    <3>8. QED
      BY <3>3, <3>5, <3>7, SMT
  <2>5. ASSUME Inv, Get
        PROVE  C!Rcv
    <3> USE Get
    <3> SUFFICES chBar' = Tail(chBar) 
      BY <2>3, PutGet DEF Get, C!Rcv
    <3> DEFINE pmc == p (-) c
    <3>2. \A i \in 1..(pmc-1) : chBar[i+1] = buf[(c + i) % N]
      BY PutGet, SMT DEF Inv, TypeOK, PCInv, chBar
    <3>3. Tail(chBar) = [i \in 1..(pmc-1) |-> buf[(c + i) % N]]
      BY <2>3, PutGet, TailDef, <3>2, Z3
    <3>4. /\ pmc' = pmc-1
          /\ \A i \in 1..(pmc-1) : (c' + i - 1) % N = (c + i) % N
      <4>1. SUFFICES ASSUME NEW i \in 1..(pmc-1) 
                     PROVE (c' + i - 1) % N = (c + i) % N
        BY PutGet, SMT
      <4>2. /\ c' \in Int
            /\ i-1 \in Int
            /\ c+1 \in Int
            /\ (c+1) + (i-1) = c + i
        BY ModDef, SMT DEF Get, (+), Inv, TypeOK, PCInv
      <4>3. (c' + i - 1) % N = ((c'%N) + ((i-1)%N))%N
        BY <4>2, ModN3, Z3
      <4>4. @ = (((c+1)%N) + ((i-1)%N))%N
        BY <4>2, Mod2N, SMT DEF Get, (+)
      <4>5. @ = ((c+1) + (i-1))%N
        BY <4>2, ModN3, Z3
      <4>7 QED
        BY <4>3, <4>4, <4>5, <4>2, ModN3, SMT
    <3>5. Tail(chBar) = [i \in 1..pmc' |-> buf[(c'+ i - 1) % N]]
      BY <3>3, <3>4, SMT
    <3>6. QED
      BY <3>5, Z3 DEF Get, chBar
  <2>6. QED
    BY <2>4, <2>5, SMT DEF Next, C!Next
<1>3. QED
  PROOF OMITTED

=============================================================================
