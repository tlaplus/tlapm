----------------------------- MODULE Quicksort05 -----------------------------
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
(*Inv == TypeOK /\ Safety *)

(* Ok, I think I got the hang of basic proof structures,
    now let's do some logic...
    clearly Safety is not the right invariant, since it is vacuously true as long as U is not empty...

    let's try this instead, which says intuitively "if there are two values in A in the wrong order,
        then there is a segment of A which they are both in and which is still on the stack to be sorted":
*)
Inv ==  /\ TypeOK
        /\ A \in PermsOf(A0)
        /\ \A i, j \in 1..N  :  (i < j /\ A[j] < A[i])
                                => \E b, t \in 1..N : <<b, t>> \in U /\ b <= i /\ j <= t

(* The documentation of WITNESS is very minimal, and the error messages are confusing:

In the following state, checking step <3>1 generates an obligation
asking me to prove that 1 \in 1..N, under the assumption that
 \E t \in 1 .. N : <<1, t>>  \in  U  /\  1  \leq  i  /\  j  \leq  t  ??

 Adding `OBVIOUS' under step <3>1 generates a syntax error ??

++++++++++++++++++++++++++++
THEOREM Spec => []Safety
<1>1 Init => Inv
    PROOF
     <2>2 SUFFICES     (Init => \A i, j \in 1..N : \E b, t \in 1..N : <<b, t>> \in U /\ b <= i /\ j <= t)
                    /\ (Init => TypeOK)
        BY DEF Inv, TypeOK
     <2>3 ASSUME Init,
                 NEW i \in 1.. N,
                 NEW j \in 1 .. N
          PROVE  \E b, t \in 1..N: <<b,t>> \in U /\ b <= i /\ j <= t
        <3>1 WITNESS 1 \in 1..N
        <3>2 WITNESS N \in 1..N
        <3>q QED
        BY <3>1, <3>2, Z3, <2>3 DEF Init
      <2>4 Init => TypeOK
        BY Z3, ConstantAssump DEF Init, TypeOK, ConstantAssump
      <2> QED
        BY <2>2, <2>3, <2>4
...
+++++++++++++++++++++++++


I'm moving to <1>3 for now:

- This example-oriented documenation is getting cumbersome: If I want to know how to use something I always have to find
    and example that uses it.
    Right now, for instance, I'd like to know how to prove something by contradiction.
    I can either state everything and hope that isabelle finds the contradiction automatically,
    however, seeing that that doesn't work with vacuously true implications I'm skeptical...

    what I really want is:
    - A list of all proof structures in alphabetical order, with a minimal syntactically correct example of their use.
    - A list of all tactics in alphabetical order annotated with the kinds of facts they can prove.

Right, <1>3 discharged, I'm moving to <1>2:

-  I'll need transitivity of PermsOf....

- I'll also restructure the proof so that the case distinction can be shared between <2>2, <2>3, and <2>4


*)

PermsOf_trans == \A a, b, c \in [1..N -> Int] : (c \in PermsOf(b) /\ b \in PermsOf(a)) => c \in PermsOf(a)
LEMMA PermsOf_trans
<1> ASSUME  NEW a\in [1..N -> Int],
            NEW b\in [1..N -> Int],
            NEW c\in [1..N -> Int],
            c \in PermsOf(b),
            b \in PermsOf(a)
    PROVE   c \in PermsOf(a)
<1>q QED
    BY DEF PermsOf_trans

THEOREM Spec => []Safety
<1>1 Init => Inv
    PROOF
     <2>2 SUFFICES     (Init => \A i, j \in 1..N : \E b, t \in 1..N : <<b, t>> \in U /\ b <= i /\ j <= t)
                    /\ (Init => TypeOK)
        BY DEF Inv, TypeOK
     <2>3 ASSUME Init,
                 NEW i \in 1.. N,
                 NEW j \in 1 .. N
          PROVE  \E b, t \in 1..N: <<b,t>> \in U /\ b <= i /\ j <= t
        <3>1 WITNESS 1 \in 1 .. N
        <3>2 WITNESS N \in 1..N
        <3>q QED
        BY <3>1, <3>2, Z3, <2>3 DEF Init
      <2>4 Init => TypeOK
        BY Z3, ConstantAssump DEF Init, TypeOK, ConstantAssump
      <2> QED
        BY <2>2, <2>3, <2>4

<1>2 Inv /\ [Next]_vars => Inv'
    <2>1 SUFFICES    (TypeOK /\ [Next]_vars => TypeOK')
                  /\ (A \in PermsOf(A0) /\ [Next]_vars => A' \in PermsOf(A0))
                  /\ (Inv /\ [Next]_vars
                      => \A i, j \in 1..N : (i < j /\ A'[j] < A'[i])
                                            => \E b, t \in 1..N : <<b, t>> \in U' /\ b <= i /\ j <= t)
          BY  DEF Inv
    <2>2 ASSUME TypeOK, [Next]_vars
         PROVE TypeOK'
         <3>1 CASE UNCHANGED vars
            BY <3>1, <2>2 DEF TypeOK, vars (* yet another one where I must mention <2>1 in its own proof... ? *)
         <3>2 CASE Next
            <4>1 SUFFICES ASSUME TypeOK, U#{},
                                 NEW b \in 1 .. N,
                                 NEW t \in 1 .. N,
                                 <<b,t>> \in U,
                                 IF b  #  t
                                    THEN \E p \in b .. t  -  1 :
                                         /\ A'  \in  Partitions(A, p, b, t)
                                         /\ U'= (U  \  {<<b, t>>}) \union {<<b, p>>, <<p  +  1, t>>}
                                    ELSE /\ U'  =  U  \  {<<b, t>>}
                                         /\ A'  =  A
                           PROVE TypeOK'
                 BY <2>2, <3>1, <4>1 DEF Next (* again, this only goes through when I put <2>2 -- which I'm proving here... ?? *)
             <4>2 ASSUME TypeOK, U # {},
(*  For some reason I can't assume NEW b and t here? But the only other place where they are introduced is <4>1?
    There is something I'm not getting about scopes of variables...
                         NEW b \in 1 .. N,
                         NEW t \in 1 .. N,
*)                         <<b,t>> \in U,
                         IF b  #  t
                             THEN \E p \in b .. t  -  1 :
                                  /\ A'  \in  Partitions(A, p, b, t)
                                  /\ U'= (U  \  {<<b, t>>}) \union {<<b, p>>, <<p  +  1, t>>}
                             ELSE /\ U'  =  U  \  {<<b, t>>}
                                  /\ A'  =  A
                  PROVE TypeOK'
                <5>1 CASE b = t
                    BY Z3, <4>2, <5>1 DEF TypeOK
                <5>2 CASE b # t
 (* this seems like it should be good enough here... ? :  BY Z3, <4>2, <5>1 DEF TypeOK  *)
                    <6>1 SUFFICES ASSUME TypeOK,
                                         NEW p \in b .. t-1,
                                         A' \in Partitions(A, p, b, t),
                                         U'= (U  \  {<<b, t>>}) \union {<<b, p>>, <<p  +  1, t>>}
                                  PROVE A' \in [1..N-> Int] /\ U' \in SUBSET ((1..N) \X (1..N))
                        BY <4>2, <5>2 DEF TypeOK
                    <6>2 A' \in [1..N -> Int]
                        BY <6>1, Z3 DEF TypeOK, Partitions, PermsOf (* aha, Z3 can prove this!! *)
                    <6>3 U' \in SUBSET ((1..N) \X (1..N))
(*                        BY <6>1, Z3 DEF TypeOK (* then why can't it prove this ?!? *) *)
                        <7>1 SUFFICES {<<b,p>>, <<p+1, t>>} \in SUBSET ((1..N) \X (1..N))
                            BY <6>1 DEF TypeOK
                        <7>2 {<<b,p>>, <<p+1, t>>} \in SUBSET ((1..N) \X (1..N))
                            (* And why doesn't Z3 prove this one ... ?*)
                            <8>1 SUFFICES <<b, p>> \in (1..N) \X (1..N)
                                       /\ <<p+1, t>> \in (1..N) \X (1..N)
                                OBVIOUS
 (* How is this not obvious when the above is ?????
                            <8>1 SUFFICES b \in 1.. N
                                       /\ p \in 1..N
                                       /\ p+1 \in 1..N
                                       /\ t \in 1..N
                                OBVIOUS
 *)
 (* Now this gives me a Parse Error: "Encountered "<8>3" at line ... in moduel Quicksort05" ???
                            <8>2 <<b, p> \in (1..N) \X (1..N)
                            <8>3 <<p+1, t>> \in (1..N) \X (1..N)
  *)
                            <8>2 <<b, p>> \in (1..N) \X (1..N)
                                <9>1 SUFFICES b \in 1..N /\ p \in 1..N
                                    OBVIOUS
                                <9>2 b \in 1..N
                                    OBVIOUS
                                <9>3 p \in 1..N
                                  (*  BY Z3  Honestly, this is not clear ??? *)
                                  <10>1 SUFFICES 1 <= b /\ t - 1 <= N
                                    BY Z3 (* I Give Up *)
                                  <10>2 1 <= b
                                    BY Z3
                                  <10>3 t-1 <= N (* again, I think this should just be `BY Z3' ?? *)
                                    <11>1 SUFFICES t <= N
                                        BY Z3 (* ??? *)
                                    <11>2 t <= N
                                        BY Z3
                                    <11>q QED
                                        BY <11>1, <11>2
                                  <10>q QED
                                    BY <10>1, <10>2, <10>3
                                <9>q QED
                                    BY <9>1, <9>2, <9>3
                            <8>3 <<p+1, t>> \in (1..N) \X (1..N)
                                <9>1 SUFFICES p+1 \in 1..N /\ t \in 1..N
                                    OBVIOUS
                                <9>2 t \in 1..N
                                    OBVIOUS
                                <9>3 p+1 \in 1..N (* when <8>2 is solved, copy, paste & tweak... *)
                                <9>q QED
                                    BY <9>1, <9>2, <9>3
                            <8>q QED
                                BY <8>1, <8>2, <8>3
                        <7>q QED
                            BY <7>1, <7>2
                    <6>q QED
                        BY <6>1, <6>2, <6>3
                 <5>q QED
                    BY <5>1, <5>2
            <4>q QED
                BY <4>1, <4>2
         <3>q QED
            BY <3>1, <3>2, <2>2 (* this is a case where I must mention <2>2 in its own proof... ?? *)
    <2>3 ASSUME A \in PermsOf(A0), [Next]_vars
         PROVE A' \in PermsOf(A0)
         <3>1 CASE UNCHANGED vars
            BY <2>3  DEF vars (* what is the tactic that will get this done ? (I'm assuming there is one...?) *)
         <3>2 CASE Next






            BY PermsOf_trans, <2>3, <3>2 DEF vars, PermsOf_trans, Next

         <3>q QED
            BY <3>1, <3>2, <2>3
    <2>4 ASSUME Inv, [Next]_vars
         PROVE \A i, j \in 1..N : (i < j /\ A'[j] < A'[i])
                                            => \E b, t \in 1..N : <<b, t>> \in U' /\ b <= i /\ j <= t
    <2>q QED
    BY <2>1, <2>2, <2>3, <2>4

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
            BY <2>3 DEF Inv
         <3>2 ~ \E b, t \in N : <<b,t>> \in U /\ b <= i /\ j <= t
            BY <2>3
         <3>3 ~(A[j] < A[i]) => A[i] \leq A[j]
            BY Z3
         <3>4 ~(A[j] < A[i])
            BY <3>1, <3>2
         <3>q QED
         BY  <2>2, <3>3, <3>4 DEF Inv, IsSorted
    <2>q QED
        BY <2>1, <2>2, <2>3 DEF IsSorted


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

