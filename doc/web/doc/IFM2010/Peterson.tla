--------------------------- MODULE Peterson  ----------------------------
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

Next == \E self \in {0,1}: proc(self)

Spec == Init /\ [][Next]_vars

MutualExclusion == ~ (pc[0] = "cs" /\ pc[1] = "cs")


TypeOK == /\ pc \in [{0,1} -> {"a0", "a1", "a2", "a3a", "a3b", "cs", "a4"}]
          /\ turn \in {0, 1}
          /\ flag \in [{0,1} -> BOOLEAN]

I == \A i \in {0, 1} :
       /\ (pc[i] \in {"a2", "a3a", "a3b", "cs", "a4"} => flag[i])
       /\ (pc[i] \in {"cs", "a4"})
            => /\ pc[Not(i)] \notin {"cs", "a4"}
               /\ (pc[Not(i)] \in {"a3a", "a3b"}) => (turn = i)

FullInv == TypeOK /\ I

------------------------------------------------------------------------------

THEOREM InitME == Init => MutualExclusion
BY DEFS Init, MutualExclusion, ProcSet

LEMMA TypeCorrect == TypeOK /\ Next => TypeOK'
<1>1. ASSUME NEW i \in {0,1}
      PROVE  TypeOK /\ proc(i) => TypeOK'
  BY DEFS TypeOK, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>. QED
  BY <1>1 DEF Next

THEOREM Inductive == TypeOK /\ I /\ Next => I'
<1>1. ASSUME TypeOK,
             I,
             NEW i \in {0,1},
             proc(i)
      PROVE  I'
  <2>0. TypeOK'
  <2>1. ASSUME NEW j \in {0,1},
               pc'[j] \in {"a2", "a3a", "a3b", "cs", "a4"}
        PROVE  flag'[j]
       <3>a0. CASE a0(j)
       (*** to be continued... ***)
       <3>q. QED
  <2>2. ASSUME NEW j \in {0,1},
               pc'[j] \in {"cs", "a4"}
        PROVE pc'[Not(j)] \notin {"cs", "a4"}
  <2>3. ASSUME NEW j \in {0,1},
               pc'[j] \in {"cs", "a4"},
               pc'[Not(j)] \in {"a3a", "a3b"}
        PROVE turn' = j
  <2>. QED
    BY <2>1, <2>2, <2>3 DEF I, Not
<1>. QED
  BY <1>1 DEF Inductive, Next

THEOREM Spec => []FullInv
PROOF OMITTED

THEOREM I => MutualExclusion
BY DEFS I, MutualExclusion, Not

=============================================================================
