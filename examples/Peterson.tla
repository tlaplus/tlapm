--------------------------- MODULE Peterson  ----------------------------
(***********************************************************************)
(* This is Peterson's standard two-process mutual exclusion algorithm. *)
(* A TLA+ specification is derived from a PlusCal algorithm, then      *)
(* mutual exclusion is shown using either the SMT backend or just the  *)
(* Zenon and Isabelle backends.                                        *)
(* This example is described in more detail in:                        *)
(* D. Cousineau et al.: TLA+ Proofs. 18th Intl. Symp. Formal Methods   *)
(* (FM 2012). Springer LNCS 7436, pp. 147-154, Paris 2012.             *)
(* Available online at http://www.loria.fr/~merz/papers/fm2012.html    *)
(***********************************************************************)
EXTENDS TLAPS

Not(i) == IF i = 0 THEN 1 ELSE 0

(*******
--algorithm Peterson {
   variables flag = [i \in {0, 1} |-> FALSE], turn = 0;
   fair process (proc \in {0,1}) {
     a0: while (TRUE) {
     a1:   flag[self] := TRUE;
     a2:   turn := Not(self);
     a3a:  if (flag[Not(self)]) {goto a3b} else {goto cs} ;
     a3b:  if (turn = Not(self)) {goto a3a} else {goto cs} ;
     cs:   skip;  \* critical section
     a4:   flag[self] := FALSE;
     } \* end while
    } \* end process
  }
********)

\* BEGIN TRANSLATION
VARIABLES flag, turn, pc

vars == << flag, turn, pc >>

ProcSet == ({0,1})

Init == (* Global variables *)
        /\ flag = [i \in {0, 1} |-> FALSE]
        /\ turn = 0
        /\ pc = [self \in ProcSet |-> "a0"]

a0(self) == /\ pc[self] = "a0"
            /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ UNCHANGED << flag, turn >>

a1(self) == /\ pc[self] = "a1"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ turn' = turn

a2(self) == /\ pc[self] = "a2"
            /\ turn' = Not(self)
            /\ pc' = [pc EXCEPT ![self] = "a3a"]
            /\ flag' = flag

a3a(self) == /\ pc[self] = "a3a"
             /\ IF flag[Not(self)]
                   THEN /\ pc' = [pc EXCEPT ![self] = "a3b"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
             /\ UNCHANGED << flag, turn >>

a3b(self) == /\ pc[self] = "a3b"
             /\ IF turn = Not(self)
                   THEN /\ pc' = [pc EXCEPT ![self] = "a3a"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
             /\ UNCHANGED << flag, turn >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "a4"]
            /\ UNCHANGED << flag, turn >>

a4(self) == /\ pc[self] = "a4"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "a0"]
            /\ turn' = turn

proc(self) == a0(self) \/ a1(self) \/ a2(self) \/ a3a(self) \/ a3b(self)
                 \/ cs(self) \/ a4(self)

Next == (\E self \in {0,1}: proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {0,1} : WF_vars(proc(self))

\* END TRANSLATION

\* The following predicate defines mutual exclusion of Peterson's algorithm.
MutualExclusion == ~(pc[0] = "cs"  /\ pc[1] = "cs")

NeverCS == pc[0] # "cs"

Wait(i) == (pc[i] = "a3a") \/ (pc[i] = "a3b")
CS(i) == pc[i] = "cs"
Fairness == WF_vars(proc(0)) /\ WF_vars(proc(1))
FairSpec == Spec /\ Fairness
Liveness1 == []<>CS(0)
Liveness == (Wait(0) ~> CS(0)) /\ (Wait(1) ~> CS(1))

-----------------------------------------------------------------------------

\* The proof

TypeOK == /\ pc \in [{0,1} -> {"a0", "a1", "a2", "a3a", "a3b", "cs", "a4"}]
          /\ turn \in {0, 1}
          /\ flag \in [{0,1} -> BOOLEAN]

I == \A i \in {0, 1} :
       /\ (pc[i] \in {"a2", "a3a", "a3b", "cs", "a4"} => flag[i])
       /\ (pc[i] \in {"cs", "a4"})
            => /\ pc[Not(i)] \notin {"cs", "a4"}
               /\ (pc[Not(i)] \in {"a3a", "a3b"}) => (turn = i)

Inv == TypeOK /\ I

\* Use this specification to check with TLC that Inv is an inductive invariant.
ISpec == Inv /\ [][Next]_vars

USE DEF ProcSet

THEOREM Spec => []MutualExclusion
<1>1. Init => Inv
  BY DEF Init, Inv, TypeOK, I
<1>2. Inv /\ [Next]_vars => Inv'
\*  BY DEFS Inv, TypeOK, I, Next, proc, a0, a1, a2, a3a, a3b, cs, a4, Not, vars 
  <2> SUFFICES ASSUME Inv,
                      [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2>. USE DEF Inv, TypeOK, I, Not
  <2>1. ASSUME NEW self \in {0,1},
               a0(self)
        PROVE  Inv'
    BY <2>1 DEF a0
  <2>2. ASSUME NEW self \in {0,1},
               a1(self)
        PROVE  Inv'
    BY <2>2 DEF a1
  <2>3. ASSUME NEW self \in {0,1},
               a2(self)
        PROVE  Inv'
    BY <2>3 DEF a2
  <2>4. ASSUME NEW self \in {0,1},
               a3a(self)
        PROVE  Inv'
    BY <2>4 DEF a3a
  <2>5. ASSUME NEW self \in {0,1},
               a3b(self)
        PROVE  Inv'
    BY <2>5 DEF a3b
  <2>6. ASSUME NEW self \in {0,1},
               cs(self)
        PROVE  Inv'
    BY <2>6 DEF cs
  <2>7. ASSUME NEW self \in {0,1},
               a4(self)
        PROVE  Inv'
    BY <2>7 DEF a4
  <2>8. CASE UNCHANGED vars
    BY <2>8 DEF vars
  <2>9. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8 DEF Next, proc
<1>3. Inv => MutualExclusion
  BY DEFS Inv, I, MutualExclusion, Not
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec


\* Second proof, using just Zenon and Isabelle for the non-temporal obligations
THEOREM Spec => []MutualExclusion
<1>1. Init => Inv
  BY Zenon DEFS Init, Inv, TypeOK, I
<1>2. Inv /\ [Next]_vars => Inv'
  <2>1. SUFFICES ASSUME Inv, Next PROVE Inv'
    BY Zenon DEFS Inv, TypeOK, I, vars
  <2>2. TypeOK'
    BY Inv, Next, IsaM("auto") DEFS Inv, TypeOK, Next, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
  <2>3. I'
    <3>1. SUFFICES ASSUME NEW j \in {0,1}
                   PROVE  I!(j)'
      BY Zenon DEF I
    <3>2. PICK i \in {0,1} : proc(i)
      BY Next, Zenon DEF Next
    <3>3. CASE i=j
      BY Inv, proc(i), i=j, Zenon DEFS Inv, TypeOK, I, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
    <3>4. CASE i#j
      BY Inv, proc(i), i#j, Zenon DEFS Inv, TypeOK, I, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
    <3>5. QED
      BY <3>3, <3>4, Zenon
  <2>4. QED
    BY <2>2, <2>3, Zenon DEF Inv
<1>3. Inv => MutualExclusion
  BY Zenon DEFS Inv, I, MutualExclusion, Not
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================
