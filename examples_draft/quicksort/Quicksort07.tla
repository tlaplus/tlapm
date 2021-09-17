----------------------------- MODULE Quicksort07 -----------------------------
(***************************************************************************)
(* This module specifies a Quicksort algorithm for sorting a sequence A of *)
(* length N of integers.                                                   *)
(***************************************************************************)
EXTENDS Integers, TLAPS, FiniteSetTheorems, Utils, Bags

CONSTANT A0, N

ASSUME ConstantAssump == /\ N \in Nat \ {0}
                         /\ A0 \in [1..N -> Int]

IsSorted(B) == \A i, j \in 1..N :
(i < j) => (B[i] =< B[j])

PermsOf(Arr) ==
  LET Automorphisms(S) == { f \in [S -> S] : \A y \in S : \E x \in S : f[x] = y }

      f ** g == [x \in DOMAIN g |-> f[g[x]]]

  IN  { Arr ** f : f \in Automorphisms(DOMAIN Arr) }


Partitions(B, pivot, lo, hi) ==
{ C \in [1..N -> Int] :
    /\ (\E D \in PermsOf([i \in lo..hi |-> B[i]]) : C = [i \in 1..N |-> IF i \in lo..hi
                                                                           THEN D[i]
                                                                           ELSE B[i] ] )
    /\ \A i \in lo..pivot, j \in (pivot+1)..hi : C[i] =< C[j]
  }
(*  {C \in PermsOf(B) :
      /\ \A i \in 1..(lo-1) \cup (hi+1)..N : C[i] = B[i]
      /\ \A i \in lo..pivot, j \in (pivot+1)..hi : C[i] =< C[j] }
*)


VARIABLES A, U

TypeOK == /\ A \in [1..N -> Int]
          /\ U \in SUBSET ((1..N) \X (1..N))

vars == <<A, U>>

Init == /\ A = A0
        /\ U = { <<1, N>> }

Next ==   /\ U # {}
          /\ \E b \in 1..N, t \in 1..N :
               /\ <<b, t>> \in U
               /\ IF b # t
                    THEN \E p \in b..(t-1) :
                           /\ A' \in Partitions(A, p, b, t)
                           /\ U' = (U \ {<<b, t>>}) \cup {<<b, p>>, <<p+1, t>>}
                    ELSE /\ U' = U \ {<<b, t>>}
                         /\ A' = A

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
-----------------------------------------------------------------------------

LEMMA EverythingIsFinite_1N == \A X : IsFiniteSet({X[k] : k \in 1..N})
  <1> SUFFICES ASSUME NEW X
               PROVE  (*IsFiniteSet({X[i] : i \in 1..N})*)
                     ExistsSurjection(1..N, {X[k] : k \in 1..N})
    BY ConstantAssump, N \in Nat,  FS_NatSurjection
  <1> DEFINE Thing == {X[k] : k \in 1..N}
  <1> DEFINE W == Restrict(X, 1..N)

  <1>1 W \in Surjection(1..N, Thing)
    BY DEF Restrict, Surjection


  <1>q QED
    BY <1>1 DEF ExistsSurjection

LEMMA EverythingIsFinite == \A X : \A i, j \in 1..N : IsFiniteSet({X[k] : k \in i..j})
  <1> SUFFICES ASSUME NEW X,
                      NEW i \in 1..N,
                      NEW j \in 1..N
               PROVE  IsFiniteSet({X[k] : k \in i..j})
    OBVIOUS
  <1> DEFINE S == {X[k] : k \in 1..N}
  <1> DEFINE T == {X[k] : k \in i..j}
  <1>1 T \in SUBSET S
    <2> SUFFICES ASSUME NEW k \in i..j
                 PROVE k \in 1..N
       OBVIOUS
    <2>q QED
        BY ConstantAssump, SMT
  <1>2 IsFiniteSet(S)
    BY EverythingIsFinite_1N
  <1>q QED
    BY <1>1, <1>2, FS_Subset




Safety == (U = {}) => (A \in PermsOf(A0)) /\ IsSorted(A)

(* Inv_aux := If there are two positions i,j that point to values which are not sorted,
    then they will be sorted (i.e. there is a pair on the stack that has both i and j in range).  *)
Inv_aux == \A i, j \in 1..N  :  (i < j /\ A[j] < A[i])
                                => \E b, t \in 1..N : <<b, t>> \in U /\ b <= i /\ j <= t


Inv ==  /\ TypeOK
        /\ A \in PermsOf(A0)
        /\ Inv_aux



(* NoOverlap := There is no overlap on the stack ever: *)
NoOverlap == \A a,b \in 1..N : <<a,b>> \in U => \A i \in a..b :  \A c,d \in 1..N : <<c,d>> \in U \ {<<a,b>>} => ~ i \in c..d
LEMMA NO == Spec => []NoOverlap
<1>1 Init => NoOverlap
    BY DEF Init, NoOverlap

<1>2 ASSUME NoOverlap, [Next]_vars
     PROVE NoOverlap'
    <2>  NoOverlap
        BY <1>2
    <2>1 CASE UNCHANGED vars
        BY <2>1 DEF vars, NoOverlap

    <2>2 CASE Next
        <3> USE Next
        <3>0 PICK b,t \in 1..N : Next!2!(b,t)
            BY DEF Next


        <3>1 ASSUME b # t,
                     \E p \in b .. t  -  1 :
                          /\ A'  \in  Partitions(A, p, b, t)
                          /\ U'  =
                             (U  \  {<<b, t>>})  \union
                             {<<b, p>>, <<p  +  1, t>>}
             PROVE NoOverlap'
          <4> USE b # t (* why can I do this here, even though <3>1 has a name?? *)
          <4> SUFFICES ASSUME NEW a \in (1..N), NEW e \in (1..N),
                              <<a,e>> \in U',
                              NEW i \in (a..e),
                              NEW c \in (1..N), NEW d \in (1..N),
                              <<c,d>> \in U' \ {<<a,e>>}
                       PROVE  ~ i \in c..d
            BY DEF NoOverlap
          <4>1 PICK p \in b..t : Next!2!(b,t)!2!2!(p)
            BY <3>0, <3>1 DEF Next
          <4> U' = (U \ {<<b,t>>}) \union {<<b,p>> , <<p+1,t>>}
            BY <4>1
          <4> <<b,t>> \in U
            BY <3>0

          <4>2 CASE <<a,e>> \in U \ {<<b,t>>}
            <5> USE <<a,e>> \in U \ {<<b,t>>}
            <5>1   \A k, l \in 1 .. N :
                     <<k, l>>  \in  U  \  {<<a, e>>}  =>  \neg i  \in  k .. l
                  BY ZenonT(30) DEF NoOverlap (*fragile timeout here... if it doesn't work, try 40 *)
            <5>2 CASE <<c,d>> \in U \ {<<a,e>>}
                BY <5>1, <5>2

            <5>3 CASE <<c,d>> = <<b,p>> \/ <<c,d>> = <<p+1, t>>
                <6> USE <5>3
                <6>1 <<b,t>> \in U \ {<<a, e>>}
                    OBVIOUS
                <6> ~ i \in b..t
                    BY DEF NoOverlap

                <6>q QED
                    OBVIOUS

            <5>q QED
                BY <5>2, <5>3 DEF NoOverlap

          <4>3 CASE <<a,e>> = <<b,p>> \/ <<a,e>> = <<p+1,t>>
            <5> USE <4>3

            <5>1 CASE <<c,d>> \in U \ {<<b,t>>}
                <6> USE <5>1
                <6>2  i \in b..t
                    OBVIOUS
                <6>q QED
                    BY ONLY <<b,t>> \in U, NoOverlap, <6>2, <5>1, Zenon DEF NoOverlap

            <5>2 CASE <<c,d>> = <<b,p>> \/ <<c,d>> = <<p+1, t>>
                <6> USE <5>2
                <6>q QED
                    OBVIOUS

            <5>q QED
                BY <5>1, <5>2



          <4>q QED
            BY <4>1, <4>2, <4>3 DEF NoOverlap


        <3>2 ASSUME b = t,
                    U'  =  U  \  {<<b, t>>} /\ A'  =  A
             PROVE NoOverlap'
          <4> SUFFICES ASSUME NEW a \in (1..N), NEW e \in (1..N),
                              <<a,e>> \in U',
                              NEW i \in (a..e),
                              NEW c \in (1..N), NEW d \in (1..N),
                              <<c,d>> \in U' \ {<<a,e>>}
                       PROVE  ~ i \in c..d
            BY DEF NoOverlap
          <4>q QED
            BY <3>2 DEF NoOverlap




        <3>q QED
          BY <3>1, <3>2, <3>0 DEF Next

    <2>q QED
        BY <2>1, <2>2, <1>2

<1>q QED
    BY LS4, <1>1, <1>2 DEF Spec


LEMMA Partitions_PermsOf == \A B, C \in [1..N -> Int] : \A p, l, h \in 1..N :
                            C \in Partitions(B, p, l, h) => C \in PermsOf(B)
  <1> USE ConstantAssump
  <1> SUFFICES ASSUME NEW B \in [1..N -> Int],
                      NEW C \in [1..N -> Int],
                      NEW p \in 1..N,
                      NEW l \in 1..N,
                      NEW h \in 1..N,
                      C \in Partitions(B, p, l, h)
               PROVE  \E f \in [1..N -> 1..N] : /\ (\A y \in 1..N : \E x \in 1..N : f[x] = y)
                                                /\ C = [i \in 1..N |-> B[f[i]]]
    BY Isa DEF PermsOf
  <1>1 PICK D \in PermsOf([i \in l..h |-> B[i]]) : C = [i \in 1..N |-> IF i \in l..h
                                                                           THEN D[i]
                                                                           ELSE B[i] ]
    BY Isa  DEF Partitions
  <1>2 \A i \in l..h : C[i] = D[i]
    BY <1>1   (* why not??? *)
  <1>3 PICK g \in [l..h -> l..h] :  (\A y \in l..h : \E x \in l..h : g[x] = y)
                                  /\ D = [x \in l..h |-> B[g[x]]]
        BY DEF PermsOf
  <1> DEFINE w ==  [i \in 1..N |-> IF i \in l..h THEN g[i] ELSE i]
  <1> w \in [1..N -> 1..N]
    OBVIOUS
  <1> ASSUME NEW y \in 1..N
      PROVE \E x \in 1..N : w[x] = y

    <2> CASE y \in l..h
        <3> PICK x \in l..h : g[x] = y
            BY <1>3
        <3> x \in Int (* so it actually needed this to get the Witness statement below green... *)
            OBVIOUS
        <3> WITNESS x \in 1..N
        <3>q QED
            BY w[x] = g[x]

    <2> CASE ~ y \in l..h
        OBVIOUS
    <2>q QED
        OBVIOUS

  <1> C = [i \in 1..N |-> B[w[i]]]
    <2> SUFFICES ASSUME NEW i \in 1..N
                 PROVE C[i] = B[w[i]]
       OBVIOUS
    <2> CASE i \in l..h
        BY <1>3, <1>2
    <2> CASE ~ i \in l..h
        BY w[i] = i DEF Partitions
    <2>q QED
        OBVIOUS


  <1> QED
    OBVIOUS


(* PermsOfSetStable := Permuting does not affect the set of values in an array *)
LEMMA PermsOfSetStable == \A b, t \in 1..N : \A B, C \in [b..t -> Int] : C \in PermsOf(B) => {C[k] : k \in b..t} = {B[k] : k \in b..t}
  <1> SUFFICES ASSUME NEW b \in 1..N,
                      NEW t \in 1..N,
                      NEW B \in [b..t -> Int],
                      NEW C \in [b..t -> Int],
                      C \in PermsOf(B)
               PROVE  {C[k] : k \in b..t} = {B[k] : k \in b..t}
    OBVIOUS

  <1>1 ASSUME NEW x \in {C[k] : k \in b..t}
       PROVE  x \in {B[k] : k \in b..t}
    <2> PICK f \in [b..t -> b..t] :   (\A y \in b..t : \E z \in b..t : f[z] = y)
                                   /\ C = [i \in b..t |-> B[f[i]]]
          BY Isa DEF PermsOf
    <2> PICK i \in b..t : x = C[i]
        BY <1>1
    <2> x = B[f[i]]
        OBVIOUS
    <2>q QED
        OBVIOUS

  <1>2 ASSUME NEW x \in {B[k] : k \in b..t} (* surprisingly, here, the actuallly copied and pasted proof from <1>1 works... maybe it's not surprising, but I was surprised...*)
       PROVE  x \in {C[k] : k \in b..t}
    <2> PICK f \in [b..t -> b..t] :   (\A y \in b..t : \E z \in b..t : f[z] = y)
                                   /\ C = [i \in b..t |-> B[f[i]]]
          BY Isa DEF PermsOf
    <2> PICK i \in b..t : x = C[i]
        BY <1>1
    <2> x = B[f[i]]
        OBVIOUS
    <2>q QED
        OBVIOUS

  <1> QED
   BY <1>1, <1>2

(* PartitionsSetStable := Partitions does not affect the set of values between lo and hi

*)
LEMMA PartitionsSetStable == \A B, C \in [1..N -> Int] : \A b, p, t \in 1..N :
                                C \in Partitions(B, p, b, t) => {C[k] : k \in b..t} = {B[k] : k \in b..t}
  <1> SUFFICES ASSUME NEW B \in [1..N -> Int],
                      NEW C \in [1..N -> Int],
                      NEW b \in 1..N,
                      NEW p \in 1..N,
                      NEW t \in 1..N,
                      C \in Partitions(B, p, b, t)
               PROVE  {C[k] : k \in b..t}  = {B[k] : k \in b..t}
    OBVIOUS

  <1> USE ConstantAssump
  <1> DEFINE Cbt == [i \in b..t |-> C[i]]
  <1> DEFINE Bbt == [i \in b..t |-> B[i]]

  <1>4 Cbt \in PermsOf(Bbt)
    <2> PICK D \in PermsOf(Bbt) :  C  = [i \in 1 .. N |-> IF i  \in  b .. t THEN D[i] ELSE B[i]]
        BY DEF Partitions
    <2>1 ASSUME NEW i \in b..t
         PROVE  C[i] = D[i]
        OBVIOUS
    <2> D \in [b..t -> Int]
        BY DEF PermsOf
    <2> Cbt = D
        BY <2>1
    <2>q QED
        OBVIOUS
  <1>5 \A X, Y \in [b..t -> Int] : Y \in PermsOf(X) => {Y[k] : k \in b..t} = {X[k] : k \in b..t} (* So Zenon is quite sensitive to the order of quantifiers : switching X and Y around under the \A will break this...*)
    BY PermsOfSetStable, Zenon
  <1>8 {Cbt[k] : k \in b..t} = {Bbt[k] : k \in b..t}
      BY Cbt \in [b..t -> Int], Bbt \in [b..t -> Int], <1>4, <1>5, Zenon
  <1>6  {C[k] : k \in b..t} =  {Cbt[k] : k \in b..t}
    OBVIOUS
  <1>7  {B[k] : k \in b..t} =  {Bbt[k] : k \in b..t}
    OBVIOUS

  <1> QED
    BY <1>8, <1>6, <1>7




LEMMA PermsOf_trans == \A a, b, c \in [1..N -> Int] : (c \in PermsOf(b) /\ b \in PermsOf(a)) => c \in PermsOf(a)
<1> ASSUME  NEW a \in [1..N -> Int],
            NEW b \in [1..N -> Int],
            NEW c \in [1..N -> Int],
            c \in PermsOf(b),
            b \in PermsOf(a)
    PROVE   c \in PermsOf(a)
    <2>1 PICK f \in [1..N -> 1..N] :
            (\A y \in 1..N : \E x \in 1..N : f[x] = y)
         /\ (c = [x \in 1..N |-> b[f[x]]])
         BY Isa DEF PermsOf
    <2>2 PICK g \in [1..N -> 1..N] :
            (\A y \in 1..N : \E x \in 1..N : g[x] = y)
         /\ (b = [x \in 1..N |-> a[g[x]]])
         BY Isa DEF PermsOf
    <2> SUFFICES ASSUME TRUE
                  PROVE \E h \in [1..N -> 1..N] :
                           (\A y \in 1..N : \E x \in 1..N : h[x] = y)
                        /\ (c = [x \in 1..N |-> a[h[x]]])
        BY Isa DEF PermsOf
    <2> DEFINE h == [k \in 1..N |-> g[f[k]]]
    <2>3 WITNESS h \in [1..N -> 1..N]

    <2>4 ASSUME NEW y \in 1..N
         PROVE \E x \in 1..N : h[x] = y
         <3> PICK i \in 1..N : g[i] = y
            BY <2>2
         <3> PICK  j \in 1..N : f[j] = i
            BY <2>1
         <3>q QED
            OBVIOUS

    <2>5 c = [x \in 1..N |-> a[h[x]]]
        BY <2>1, <2>2

    <2>q QED
        BY <2>3, <2>4, <2>5
<1>q QED
    OBVIOUS


LEMMA PermsOf_refl == \A a \in [1..N -> Int] : a \in PermsOf(a)
    BY DEF PermsOf_refl, PermsOf

THEOREM Spec => []Safety
<1>1 Init => Inv
    PROOF
     <2>2 SUFFICES     (Init => A \in PermsOf(A0))
                    /\ (Init => TypeOK)
                    /\ (Init => Inv_aux)
        BY DEF Inv, TypeOK
     <2>3 ASSUME Init,
                 NEW i \in 1.. N,
                 NEW j \in 1 .. N
          PROVE  \E b, t \in 1..N: <<b,t>> \in U /\ b <= i /\ j <= t

        <3>1 <<1,N>> \in U /\ 1 <= i /\ j <= N
          BY <2>3, CVC3  DEF Init
        <3>q QED
            BY <3>1, Z3, ConstantAssump
      <2>4 Init => TypeOK
        BY Z3, ConstantAssump DEF Init, TypeOK, ConstantAssump
      <2>5 Init => A \in PermsOf(A0)
        BY PermsOf_refl, Z3, ConstantAssump DEF Init, PermsOf_refl
      <2>q QED
        BY <2>2, <2>3, <2>4, <2>5 DEF Inv_aux

<1>2 NoOverlap /\ [Next]_vars /\ Inv => Inv'
    <2>1 SUFFICES ( NoOverlap /\ Inv /\ [Next]_vars)
               => (   TypeOK'
                   /\ A' \in PermsOf(A0)
                   /\ Inv_aux' )
          BY  DEF Inv
    <2>2 ASSUME Inv, [Next]_vars, NoOverlap
         PROVE TypeOK' /\ A' \in PermsOf(A0) /\ Inv_aux'
         <3> Inv BY <2>2
         <3> USE ConstantAssump
         <3> USE NoOverlap
         <3>1 CASE UNCHANGED vars
            <4>1 TypeOK'
                BY <2>2, <3>1 DEF Inv, TypeOK, vars
            <4>2 A' \in PermsOf(A0)
                BY <2>2, <3>1 DEF Inv, vars
            <4>3 Inv_aux'
                BY <2>2, <3>1 DEF Inv, Inv_aux, vars
            <4>q QED
                BY <4>1, <4>2, <4>3, <3>1
         <3>2 CASE Next
            <4> USE Next
            <4>1 ASSUME U # {},
                        NEW b \in 1..N,
                        NEW t \in 1..N,
                        <<b,t>> \in U,
                        IF b # t
                          THEN  \E p \in b..(t-1) :
                               /\ A' \in Partitions(A, p, b, t)
                               /\ U' = (U \ {<<b, t>>}) \cup {<<b, p>>, <<p+1, t>>}
                          ELSE /\ U' = U \ {<<b, t>>}
                               /\ A' = A
                 PROVE TypeOK' /\ A' \in PermsOf(A0) /\ Inv_aux'
                <5> USE U # {}
                <5> USE <<b,t>> \in U
                <5>1 CASE b = t
                    <6> USE b = t
                    <6> A' = A
                        BY <4>1
                    <6> U' = U \ {<<b,t>>}
                        BY <4>1
                    <6>3 TypeOK'
                        BY  DEF TypeOK, Inv
                    <6>4 A' \in PermsOf(A0)
                        BY  PermsOf_trans DEF PermsOf_trans, ConstantAssump, Inv
                    <6>5 Inv_aux'
                        BY DEF Inv_aux, Inv (* ha, that's very nice, I was expecting this to be work... *)
                    <6>q QED
                        BY <6>3, <6>4, <6>5, <5>1
                <5>2 CASE b # t
                    <6> USE b # t
                    <6> SUFFICES ASSUME  NEW p \in b..(t-1),
                                A' \in Partitions(A, p, b, t),
                                U' = (U \ {<<b,t>>}) \cup {<<b,p>>, <<p+1, t>>}
                        PROVE TypeOK' /\ A' \in PermsOf(A0) /\ Inv_aux'
                         BY <4>1
                    <6>1 TypeOK'
                        <7> U' \in SUBSET ( (1..N) \X (1..N) )
                            <8> SUFFICES          U \ {<<b,t>>} \in SUBSET ((1..N) \X (1..N))
                                        /\ {<<b,p>>, <<p+1,t>>} \in SUBSET ((1..N) \X (1..N))

                                OBVIOUS
                            <8>1  U \ {<<b,t>>} \in SUBSET ((1..N) \X (1..N))
                                BY SMT DEF Inv, TypeOK
                            <8>2  {<<b,p>>, <<p+1,t>>} \in SUBSET ((1..N) \X (1..N))
                                BY SMT
                            <8>q QED
                                BY <8>1, <8>2
                        <7> A' \in [1..N -> Int]
                            BY SMT DEF Inv, TypeOK, Partitions, PermsOf
                        <7>q QED
                            BY DEF TypeOK
                    <6>2 A' \in PermsOf(A0)
                        <7> SUFFICES A' \in PermsOf(A)
                            BY PermsOf_trans, <6>1 DEF Inv, TypeOK

                       <7>q QED
                            BY <6>1, Partitions_PermsOf  DEF TypeOK, Inv

                    <6>3 Inv_aux'
                      <7> p \in 1 .. N
                        OBVIOUS

                      <7> SUFFICES ASSUME NEW i \in (1..N),
                                          NEW j \in (1..N),
                                          (i < j),
                                           A'[j] < A'[i]
                                   PROVE  <<b, p>> \in U' /\ <<p+1, t>> \in U'
                                      (*  /\ ( (b \leq i /\ j \leq p) \/ (p+1 \leq i /\ j \leq t)) *)
                                          /\ \E b_1, t_1 \in 1..N : <<b_1, t_1>> \in U' /\ b_1 <= i /\ j <= t_1
                        BY DEF Inv_aux
                      <7>1 <<b,p>> \in U' /\ <<p+1, t>> \in U'
                        OBVIOUS
                      <7>2 CASE i \in b..t /\ j \in b..t
                         <8> USE <7>2, b \leq i, j \leq t
                         <8> HIDE <7>2 (* it seems strange that a USE statement becomes green, but a HIDE statement doesn't...?*)
                         <8>1 CASE j \leq p
                              <9> USE j \leq p
                              <9> b \leq i /\ j \leq p /\ <<b, p>> \in U'
                                  OBVIOUS
                              <9>q QED
                                  OBVIOUS
                         <8>2 CASE p < i
                              <9> USE p < i
                              <9> p+1 \leq i /\ j \leq t /\ <<p+1, t>> \in U'
                                  BY SMT
                              <9>q QED
                                  OBVIOUS

                         <8>3 CASE i \leq p /\ p < j
                              <9>1 i \in b .. p
                                  BY <8>3
                              <9>2 j \in p+1..t
                                  BY <8>3
                              <9>3 A'[i] \leq A'[j]
                                  BY <9>1, <9>2 DEF Partitions
                              <9>4 CASE A'[i] < A'[j]
                                  BY <9>4 DEF Inv, TypeOK
                              <9>5 CASE A'[i] = A'[j]
                                  BY <9>5 DEF Inv, TypeOK
                              <9>q QED
                                  BY <9>3, <9>4, <9>5, SMT DEF Inv, TypeOK
                         <8>q QED
                              BY <8>1, <8>2, <8>3 DEF Inv_aux, Inv

                      <7>3 CASE ~ i \in b..t /\ ~ j \in b..t
                         <8> USE <7>3, ~ i \in b..t, ~j \in b..t
                         <8> HIDE <7>3
                         <8> A'[i] = A[i] /\ A'[j] = A[j]
                            BY DEF Partitions
                         <8>q QED
                            BY DEF Inv, Inv_aux

                      <7>4 CASE i \in b..t /\ ~ j \in b..t
                         <8> USE <7>4,  i \in b..t, ~j \in b..t
                         <8> HIDE <7>4
                         <8> USE t < j
                         <8> A'[j] = A[j]
                            BY DEF Partitions
                         <8>1 \A x \in {A[k] : k \in b..t} : A[j] >= x
                            <9> SUFFICES ASSUME NEW x \in b..t
                                         PROVE A[j] >= A[x]
                              OBVIOUS
                            <9> USE x < j
                            <9>0 A[j]  <  A[x]  => (\E m, n \in 1 .. N : <<m, n>>  \in  U  /\  m  \leq  x  /\  j  \leq  n)
                                BY DEF Inv, Inv_aux
                            <9>3  ~ (\E m, n \in 1 .. N : <<m, n>>  \in  U  /\  m  \leq  x  /\  j  \leq  n)
                                <10> SUFFICES ASSUME NEW m \in 1..N,
                                                     NEW n \in 1..N,
                                                     <<m,n>> \in U
                                              PROVE ~ m <= x \/ ~ j <= n
                                    OBVIOUS
                                <10>1 CASE <<m,n>> = <<b,t>>
                                    BY <10>1

                                <10>2 CASE <<m,n>> # <<b,t>>
                                    BY <10>2, ~ x \in m..n DEF NoOverlap

                                <10>q QED
                                    BY <10>1, <10>2
                            <9>4 ~ A[j] < A[x] => A[j] >= A[x]
                                OBVIOUS
                            <9>q QED
(* In this situation "BY <9>0, <9>3" doesn't solve the problem, and it took me a whilte to figure out,
    that I need to explicitly separate logic from math, by providing <9>4... *)
                                BY <9>0, <9>3, <9>4

                             <8>2 \A b_1, p_1, t_1 \in 1 .. N :
                                    A' \in Partitions(A, p_1, b_1, t_1) =>
                                    {A'[k] : k \in b_1..t_1} = {A[k] : k \in b_1..t_1}
                                BY ONLY  <6>1, A \in [1..N -> Int], p \in 1..N,  PartitionsSetStable DEF TypeOK, Inv (* why does this not work?? *)
                             <8>3   {A'[k] : k \in b..t} = {A[k] : k \in b..t}
                                BY <8>2, <6>1 DEF TypeOK, Inv
                             <8>4 A'[i] \in {A[k]: k \in b..t}
                                BY <8>3
                             <8>5 A'[j] >= A'[i]
                                BY <8>4, <8>1
                         <8>q QED
                            BY <7>1, <8>5,  <6>1 DEF TypeOK
                      <7>5 CASE ~ i \in b..t /\ j \in b..t
                         <8> USE <7>5, ~ i \in b..t, j \in b..t
                         <8> HIDE <7>5
                         <8> USE i < b
                         <8> A'[i] = A[i]
                            BY DEF Partitions
                         <8>1 \A x \in {A[k] : k \in b..t} : A[i] <= x
                            <9> SUFFICES ASSUME NEW x \in b..t
                                         PROVE A[i] <= A[x]
                              OBVIOUS
                            <9> USE x > i
                            <9>0 A[i]  >  A[x]  => (\E m, n \in 1 .. N : <<m, n>>  \in  U  /\  m  \leq  i  /\  x  \leq  n)
                                BY DEF Inv, Inv_aux
                            <9>3  ~ (\E m, n \in 1 .. N : <<m, n>>  \in  U  /\  m  \leq  i  /\  x  \leq  n)
                                <10> SUFFICES ASSUME NEW m \in 1..N,
                                                     NEW n \in 1..N,
                                                     <<m,n>> \in U
                                              PROVE ~ m <= i \/ ~ x <= n
                                    OBVIOUS
                                <10>1 CASE <<m,n>> = <<b,t>>
                                    BY <10>1

                                <10>2 CASE <<m,n>> # <<b,t>>
                                    BY <10>2, ~ x \in m..n DEF NoOverlap

                                <10>q QED
                                    BY <10>1, <10>2
                            <9>4 ~ A[i] > A[x] => A[i] <= A[x]
                                OBVIOUS
                            <9>q QED
(* In this situation "BY <9>0, <9>3" doesn't solve the problem, and it took me a whilte to figure out,
    that I need to explicitly separate logic from math, by providing <9>4... *)
                                BY <9>0, <9>3, <9>4

                             <8>2 \A b_1, p_1, t_1 \in 1 .. N :
                                    A' \in Partitions(A, p_1, b_1, t_1) =>
                                    {A'[k] : k \in b_1..t_1} = {A[k] : k \in b_1..t_1}
                                BY ONLY  <6>1, A \in [1..N -> Int], p \in 1..N,  PartitionsSetStable DEF TypeOK, Inv (* why does this not work?? *)
                             <8>3   {A'[k] : k \in b..t} = {A[k] : k \in b..t}
                                BY <8>2, <6>1 DEF TypeOK, Inv
                             <8>4 A'[j] \in {A[k]: k \in b..t}
                                BY <8>3
                             <8>5 A'[j] >= A'[i]
                                BY <8>4, <8>1
                         <8>q QED
                            BY <7>1, <8>5,  <6>1 DEF TypeOK

                      <7>q QED
                        BY <7>2, <7>3, <7>4, <7>5
                   <6>q QED
                        BY <6>1, <6>2, <6>3, <5>2
              <5>q QED
                    BY <5>1, <5>2
           <4>q QED
                BY  <4>1, <3>2, <2>2 DEF Next, Inv_aux
        <3>q QED
            BY <3>1, <3>2, <2>2 DEF Inv
     <2>q QED
       BY <2>1, <2>2

<1>3 Inv => Safety
   <2>1 SUFFICES ASSUME Inv, U = {}
                 PROVE A \in PermsOf(A0) /\ IsSorted(A)
      BY DEF Safety
   <2>2 A \in PermsOf(A0)
     BY <2>1 DEF Inv
   <2>3 ASSUME NEW i \in 1..N,
               NEW j \in 1..N,
               i < j
        PROVE A[i] \leq A [j]
        <3>1 ~ (A[j] < A[i]) \/ \E b, t \in N : <<b,t>> \in U /\ b <= i /\ j <= t
           BY <2>1, <2>3 DEF Inv, Inv_aux
        <3>2 ~ \E b, t \in N : <<b,t>> \in U /\ b <= i /\ j <= t
           BY <2>1
        <3>q QED  BY <3>1, <3>2, <2>3, Z3 DEF Inv, TypeOK
   <2>q QED
       BY <2>1, <2>2, <2>3 DEF IsSorted

<1>4 QED
    BY  LS4, <1>1, <1>2, <1>3 , NO DEF Spec

=============================================================================

