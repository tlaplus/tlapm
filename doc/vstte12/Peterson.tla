------------------------------ MODULE Peterson ------------------------------
EXTENDS TLAPS
Not(i) == IF i = 0 THEN 1 ELSE 0

(***************************************************************************
The translation of this algorithm has been modified by hand.  Do not run the 
translator on it.  RawPeterson.tla contains the actual translation. 

- -algorithm Peterson {
   variables flag = [i \in {0, 1} |-> FALSE], turn = 0;
   process (proc \in {0,1}) {
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
 ***************************************************************************)
\* Simplified the translation by the following changes:
\* - Eliminated the definition 
\*      ProcSet == ({0,1})
\*   and replaced the single instances of ProcSet with its definition.
\*
\* - Eliminated a comment added by the translation
\*
\* - Changed the conjunction
\*       pc = [self \in {0, 1} |-> CASE self \in {0,1} -> "a0"]
\*   in the Init predicate to
\*       pc = [self \in {0, 1} |-> "a0"]
\*
\* - Removed some prefix /\ operators in a bulleted list 
\*   consisting of a single conjunct.
\*
\* - Removed a TRUE conjunct.
\*
\* - Removed unnecessary parentheses in definition of Next

\* BEGIN TRANSLATION
VARIABLES flag, turn, pc
vars == << flag, turn, pc >>

Init == /\ flag = [i \in {0, 1} |-> FALSE]
        /\ turn = 0
        /\ pc = [self \in {0, 1} |-> "a0"]

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
                   THEN pc' = [pc EXCEPT ![self] = "a3b"]
                   ELSE pc' = [pc EXCEPT ![self] = "cs"]
             /\ UNCHANGED << flag, turn >>

a3b(self) == /\ pc[self] = "a3b"
             /\ IF turn = Not(self)
                   THEN pc' = [pc EXCEPT ![self] = "a3a"]
                   ELSE pc' = [pc EXCEPT ![self] = "cs"]
             /\ UNCHANGED << flag, turn >>

cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "a4"]
            /\ UNCHANGED << flag, turn >>

a4(self) == /\ pc[self] = "a4"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "a0"]
            /\ turn' = turn

proc(self) == a0(self) \/ a1(self) \/ a2(self) \/ a3a(self) \/ a3b(self)
                 \/ cs(self) \/ a4(self)

Next == \E self \in {0,1}: proc(self)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in {0, 1} : pc[self] = "Done")

\* END TRANSLATION

MutualExclusion ==  (pc[0] # "cs") \/ (pc[1] # "cs")

TypeOK == /\ pc \in [{0,1} -> {"a0","a1","a2","a3a","a3b","cs","a4"}]
          /\ turn \in {0, 1}
          /\ flag \in [{0,1} -> BOOLEAN]

I == \A i \in {0, 1} :
        /\ (pc[i] \in {"a2", "a3a", "a3b", "cs", "a4"} => flag[i])
        /\ (pc[i] \in {"cs", "a4"})
             => /\ pc[Not(i)] \notin {"cs", "a4"}
                /\ (pc[Not(i)] \in {"a3a", "a3b"}) => (turn = i)

Inv == TypeOK /\ I
------------------------------------------------------------------

THEOREM Spec => []MutualExclusion
<1>1. Init => Inv
  BY DEF Init, Inv, I, TypeOK
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, Next
               PROVE Inv'
    BY DEF vars, Inv, TypeOK, I 
  <2>1. TypeOK'
    BY DEF Inv, TypeOK, Next, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
  <2>2. I'
    <3>1. PICK i \in {0,1} : proc(i)
      BY DEF Next
    <3>2. SUFFICES ASSUME NEW j \in {0,1}
                   PROVE  I!(j)'
      BY DEF I
    <3>3. CASE i = j
      BY <2>1, <3>1, <3>3 DEF Inv, I,TypeOK,proc,a0,a1,a2,a3a,a3b,
                              cs,a4,Not
    <3>4. CASE i # j
      BY <2>1, <3>1, <3>4 DEF Inv, I,TypeOK,proc,a0,a1,a2,a3a,a3b,
                              cs,a4,Not
    <3>5. QED
      BY <3>3, <3>4
  <2>3. QED
    BY <2>1, <2>2 DEF Inv
<1>3. Inv => MutualExclusion
  BY DEF MutualExclusion, Inv, I, TypeOK, Not
<1>4. QED
  PROOF OMITTED

=============================================================================
\* Modification History
\* Last modified Fri Sep 09 10:10:49 PDT 2011 by lamport
\* Created Tue Sep 06 11:20:54 PDT 2011 by lamport
