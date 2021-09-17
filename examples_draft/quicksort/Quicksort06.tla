----------------------------- MODULE Quicksort06 -----------------------------
(***************************************************************************)
(* This module specifies a Quicksort algorithm for sorting a sequence A of *)
(* length N of integers.                                                   *)
(***************************************************************************)
EXTENDS Integers, TLAPS

CONSTANT A0, N

ASSUME ConstantAssump == /\ N \in Nat \ {0}
                         /\ A0 \in [1..N -> Int]

IsSorted(B) == \A i, j \in 1..N : (i < j) => (B[i] =< B[j])

PermsOf(Arr) ==
  LET Automorphisms(S) == { f \in [S -> S] :
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { Arr ** f : f \in Automorphisms(DOMAIN Arr) }

Partitions(B, pivot, lo, hi) ==
  {C \in PermsOf(B) :
      /\ \A i \in 1..(lo-1) \cup (hi+1)..N : C[i] = B[i]
      /\ \A i \in lo..pivot, j \in (pivot+1)..hi : C[i] =< C[j] }

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
Safety == (U = {}) => (A \in PermsOf(A0)) /\ IsSorted(A)

Inv_aux == \A i, j \in 1..N  :  (i < j /\ A[j] < A[i])
                                => \E b, t \in 1..N : <<b, t>> \in U /\ b <= i /\ j <= t


Inv ==  /\ TypeOK
        /\ A \in PermsOf(A0)
        /\ Inv_aux


LEMMA PermsOf_trans == \A a, b, c \in [1..N -> Int] : (c \in PermsOf(b) /\ b \in PermsOf(a)) => c \in PermsOf(a)
<1> ASSUME  NEW a\in [1..N -> Int],
            NEW b\in [1..N -> Int],
            NEW c\in [1..N -> Int],
            c \in PermsOf(b),
            b \in PermsOf(a)
    PROVE   c \in PermsOf(a)
    BY DEF PermsOf_trans, PermsOf
<1>q QED
    BY DEF PermsOf_trans, PermsOf

LEMMA TRUE BY Isa

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

<1>2 Inv /\ [Next]_vars => Inv'
    <2>1 SUFFICES (Inv /\ [Next]_vars)
               => (   TypeOK'
                   /\ A' \in PermsOf(A0)
                   /\ Inv_aux' )
          BY  DEF Inv
    <2>2 ASSUME Inv, [Next]_vars
         PROVE TypeOK' /\ A' \in PermsOf(A0) /\ Inv_aux'
         <3> USE Inv
         <3> USE ConstantAssump
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
            <4>1 ASSUME U # {},
                        NEW b \in 1..N,
                        NEW t \in 1..N,
                        IF b # t
                          THEN  \E p \in b..(t-1) :
                               /\ A' \in Partitions(A, p, b, t)
                               /\ U' = (U \ {<<b, t>>}) \cup {<<b, p>>, <<p+1, t>>}
                          ELSE /\ U' = U \ {<<b, t>>}
                               /\ A' = A
                 PROVE TypeOK' /\ A' \in PermsOf(A0) /\ Inv_aux'
                <5>1 CASE b = t
  (* I tried to do the following here, but got an error:
  +++++++++++++++
                   <6> HAVE A' = A
                   <6> HAVE U' = U \ {<<b,t>>}
  ---------------
"  Error: this HAVE step is applied to the following goal, which is not an implication:
  vars'  /\  U'  \in  Partitions(N)  /\  Inv' "

  The guide explainst that I can only HAVE things when the current goal is an implication.
  Why is the current goal not equal to "TypeOK' /\ A' \in PermsOf(A0) /\ Inv_aux'" though?

  *)
                    <6>1 A' = A
                        BY <4>1, <5>1
                    <6>2 U' = U \ {<<b,t>>}
                        BY <4>1, <5>1
                    <6>3 TypeOK'
                        BY <4>1, <6>1, <6>2 DEF TypeOK, Inv
                    <6>4 A' \in PermsOf(A0)
                        BY <6>1, PermsOf_trans DEF PermsOf_trans, ConstantAssump, Inv
                    <6>5 Inv_aux'
                        BY DEF Inv_aux, Inv
                    <6>q QED
                        BY <6>3, <6>4, <6>5, <5>1
                <5>2 CASE b # t
                    <6>1 TypeOK'
                    <6>2 A' \in PermsOf(A0)
                    <6>3 Inv_aux'
                    <6>q QED
                        BY <6>1, <6>2, <6>3, <5>2
                <5>q QED
                    BY <5>1, <5>2
            <4>q QED
                BY <4>1, <3>2, <2>2 DEF Next
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
(*
<1>3 Inv => Safety
    <2>1 SUFFICES ASSUME Inv, U = {}
                  PROVE A \in PermsOf(A0) /\ IsSorted(A)
       BY DEF Safety
    <2>2 ASSUME Inv
         PROVE A \in PermsOf(A0)
         BY <2>2 DEF Inv
    <2>3 ASSUME Inv,
                U = {},
                NEW i \in 1..N,
                NEW j \in 1..N,
                i < j
         PROVE A[i] \leq A [j]
         <3>1 ~ (A[j] < A[i]) \/ \E b, t \in N : <<b,t>> \in U /\ b <= i /\ j <= t
            BY <2>3 DEF Inv, Inv_aux
         <3>2 ~ \E b, t \in N : <<b,t>> \in U /\ b <= i /\ j <= t
            BY <2>3
         <3>3 ~(A[j] < A[i]) => A[i] \leq A[j]
            BY Z3
         <3>4 ~(A[j] < A[i])
            BY <3>1, <3>2
         <3>q QED
         BY  <2>3, <3>4, Z3 DEF Inv, TypeOK
    <2>q QED
        BY <2>1, <2>2, <2>3 DEF IsSorted
*)
<1>4 QED
    BY  LS4, <1>1, <1>2, <1>3  DEF Inv, Spec

















   (* Side Notes:
    - It is annoying that the parser errors don't wrap around lines and I don't seem to be able to sort windows in the toolbox, so I can have them below the obligations...

    - I typed Ctrl-w (emacs-person that I am) and lost the text window somehow...

    - Why do I not get any interesting obligations, when typing C-g C-g in the following state:
++++++++++
THEOREM Spec => []Safety

<1> SUFFICES ASSUME Spec
             PROVE []Safety
<1>1 []Safety

<1> QED
    BY <1>1, LS4"
+++++++++++
    ??

  - The fact that the prover sometimes doesn't launch on C-g C-g is very annoying...

  - Highlighting matching parantheses would be helpful...

  - For some reason my touchpad's righ mouse button doesn't open the menu;
    given that the key shortcuts are very unstable, it would be good to
    be able to get at things from the main menu

  - It would be useful to be able to `print' definitions like Safety -- scolling back and forth in the middle of a long proof takes time...

  - the little `+' and `-' in the sidebar to hide parts of the proof appears and disappears apparently randomly... ?

  - It is not clear to me at all, when I'm allowed to mention somethething in its own proof and when not.
    e.g. in step <1>3 - <2>2 I have to put `<2>2' under the `BY' in order for it to go through ...


   *)


=============================================================================

