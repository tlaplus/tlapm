--------------------------- MODULE peterson_test  ----------------------------
EXTENDS TLAPS

Not(i) == IF i = 0 THEN 1 ELSE 0

(*******
--algorithm Peterson {
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
********)

\* BEGIN TRANSLATION
VARIABLES flag, turn, pc

vars == << flag, turn, pc >>

ProcSet == ({0,1})

Init == (* Global variables *)
        /\ flag = [i \in {0, 1} |-> FALSE]
        /\ turn = 0
        /\ pc = [self \in ProcSet |-> CASE self \in {0,1} -> "a0"]

a0(self) == /\ pc[self] = "a0"
            /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ UNCHANGED << flag, turn >>

a1(self) == /\ pc[self] = "a1"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ UNCHANGED turn

a2(self) == /\ pc[self] = "a2"
            /\ turn' = Not(self)
            /\ pc' = [pc EXCEPT ![self] = "a3a"]
            /\ UNCHANGED flag

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
            /\ UNCHANGED turn

proc(self) == a0(self) \/ a1(self) \/ a2(self) \/ a3a(self) \/ a3b(self)
                 \/ cs(self) \/ a4(self)

Next == (\E self \in {0,1}: proc(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

Safe == \E i \in {0, 1} : pc[i] # "cs"

Live == \A i \in {0, 1} : []<>(pc[i] = "cs")
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

FullInv == TypeOK /\ I

ISpec == FullInv /\ [][Next]_vars

THEOREM NeverDone == TypeOK /\ (\A self \in ProcSet: pc[self] = "Done") => FALSE
BY DEFS TypeOK, ProcSet

THEOREM TypeCorrect == TypeOK /\ Next => TypeOK'
<1>1. ASSUME NEW i \in {0,1}
      PROVE  TypeOK /\ proc(i) => TypeOK'
  BY Isa DEFS TypeOK, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>. QED
  BY <1>1, NeverDone DEF Next

THEOREM Inductive == TypeOK /\ I /\ Next => I'
<1>1. ASSUME TypeOK,
             I,
             NEW i \in {0,1},
             proc(i)
      PROVE  I'
  <2> USE <1>1 DEF TypeOK
  <2>0. TypeOK'
    BY TypeOK, Next, TypeCorrect DEF Next
  <2>1. ASSUME NEW j \in {0,1},
               pc'[j] \in {"a2", "a3a", "a3b", "cs", "a4"}
        PROVE  flag'[j]
    <3> USE <2>1 DEF I
    <3>a0. CASE a0(i)
       BY <3>a0 DEF a0
    <3>a1. CASE a1(i)
       BY <3>a1 DEF a1
    <3>a2. CASE a2(i)
       BY <3>a2 DEF a2
    <3>a3a. CASE a3a(i)
      <4>0. USE <3>a3a
      <4>1. CASE i = j
        BY <4>1 DEFS a3a
      <4>2. CASE i # j
        BY <4>2 DEFS a3a
      <4>. QED
        BY <4>1, <4>2
    <3>a3b. CASE a3b(i)
      <4>0. USE <3>a3b
      <4>1. CASE i = j
        BY <4>1 DEFS a3b
      <4>2. CASE i # j
         BY <4>2 DEF a3b
      <4>. QED
        BY <4>1, <4>2
    <3>cs. CASE cs(i)
       BY <3>cs DEF cs
    <3>a4. CASE a4(i)
      BY <3>a4 DEF a4
    <3>. QED
      BY <3>a0, <3>a1, <3>a2, <3>a3a, <3>a3b, <3>cs, <3>a4 DEF proc
  <2>2. ASSUME NEW j \in {0,1},
               pc'[j] \in {"cs", "a4"}
        PROVE pc'[Not(j)] \notin {"cs", "a4"}
    <3>0. USE <2>2 DEFS I, Not
    <3>3. j \in DOMAIN pc
      BY DEF TypeOK
    <3>6. j \in DOMAIN flag
      BY DEF TypeOK
    <3>a0. CASE a0(i)
      BY <3>a0 DEF a0
    <3>a1. CASE a1(i)
       BY <3>a1 DEF a1
    <3>a2. CASE a2(i)
       BY <3>a2 DEF a2
    <3>a3a. CASE a3a(i)
      <4>0. USE <3>a3a DEF a3a
      <4>1. CASE flag[Not(i)]
        BY <4>1
      <4>2. CASE ~flag[Not(i)]
        BY <4>2
      <4>3. QED
        BY <4>1, <4>2
    <3>a3b. CASE a3b(i)
      BY <3>a3b DEF a3b
    <3>cs. CASE cs(i)
       BY <3>cs DEF cs
    <3>a4. CASE a4(i)
      BY <3>a4 DEF a4
    <3>. QED
      BY <3>a0, <3>a1, <3>a2, <3>a3a, <3>a3b, <3>cs, <3>a4 DEF proc
  <2>3. ASSUME NEW j \in {0,1},
               pc'[j] \in {"cs", "a4"},
               pc'[Not(j)] \in {"a3a", "a3b"}
        PROVE turn' = j
    <3>. USE <2>3 DEF I, Not
    <3>a0. CASE a0(i)
      BY <3>a0 DEF a0
    <3>a1. CASE a1(i)
      BY <3>a1 DEF a1
    <3>a2. CASE a2(i)
      BY <3>a2 DEF a2
    <3>a3a. CASE a3a(i)
       <4>0. USE <3>a3a DEF a3a
       <4>1. CASE i = j
         BY <4>1
       <4>2. CASE i = Not(j)
         BY <4>2
       <4>3. QED
         BY <4>1, <4>2
    <3>a3b. CASE a3b(i)
       <4>0. USE <3>a3b DEF a3b
       <4>1. CASE i = j
          BY <4>1
       <4>2. CASE i = Not(j)
          BY <4>2
       <4>3. QED
          BY <4>1, <4>2
    <3>cs. CASE cs(i)
       BY <3>cs DEF cs
    <3>a4. CASE a4(i)
       BY <3>a4 DEF a4
    <3>. QED
      BY <3>a0, <3>a1, <3>a2, <3>a3a, <3>a3b, <3>cs, <3>a4 DEF proc
  <2>. QED
    BY <2>1, <2>2, <2>3 DEF I, Not
<1>. QED
  BY <1>1, NeverDone DEF Inductive, Next

THEOREM Spec => []FullInv
<1>1. Init => FullInv
  BY DEFS Init, TypeOK, I, ProcSet, FullInv
<1>2. FullInv /\ [Next]_vars => FullInv'
  BY Inductive, TypeCorrect
  DEFS TypeOK, I, Next, ProcSet, FullInv, vars, Not
<1>3. QED
  OMITTED \*BY <1>1, <1>2, RuleInvImplication DEF Spec

MutualExclusion == ~ (pc[0] = "cs" /\ pc[1] = "cs")

THEOREM I => MutualExclusion
BY DEFS I, MutualExclusion, Not

=============================================================================
