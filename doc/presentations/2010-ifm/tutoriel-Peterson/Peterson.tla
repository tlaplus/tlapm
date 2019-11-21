--------------------------- MODULE Peterson  ----------------------------
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

VARIABLES flag, turn, pc

vars == << flag, turn, pc >>

Init == (* Global variables *)
        /\ flag = [i \in {0, 1} |-> FALSE]
        /\ turn = 0
        /\ pc = [self \in {0,1} |-> "a0"]

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
            /\ pc' = [pc EXCEPT ![self] = "a4"]
            /\ UNCHANGED << flag, turn >>

a4(self) == /\ pc[self] = "a4"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "a0"]
            /\ UNCHANGED turn

proc(self) == a0(self) \/ a1(self) \/ a2(self) \/ a3a(self) \/ a3b(self) \/ cs(self) \/ a4(self)

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

(* The invariant implies the correctness property, mutual exclusion. *)
THEOREM FullInvME == FullInv => MutualExclusion
BY DEFS FullInv, I, MutualExclusion, Not

(* The invariant holds in the initial state. *)
THEOREM InitFullInv == Init => FullInv
BY DEFS Init, FullInv, TypeOK, I

(* The next-state relation preserves type correctness. *)
LEMMA TypeCorrect == TypeOK /\ Next => TypeOK'
BY Auto DEFS TypeOK, Next, proc, a0, a1, a2, a3a, a3b, cs, a4, Not

(* The next-state relation preserves the invariant I, assuming type correctness *)
THEOREM Inductive == TypeOK /\ I /\ Next => I'
<1>1. SUFFICES ASSUME TypeOK, I, Next
               PROVE  I'
  OBVIOUS
<1>2. TypeOK'
  BY <1>1, TypeCorrect
<1>3. PICK i \in {0,1} : proc(i)
  BY <1>1 DEF Next
<1>4. SUFFICES ASSUME NEW j \in {0,1}
               PROVE  I!(j)'
  BY DEF I
<1>5. CASE i = j
  BY <1>1, <1>2, <1>3, <1>5, SlowestZenon DEFS I, TypeOK, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>6. CASE i # j
  BY <1>1, <1>2, <1>3, <1>6, SlowestZenon DEFS I, TypeOK, proc, a0, a1, a2, a3a, a3b, cs, a4, Not
<1>q. QED
  BY <1>5, <1>6

THEOREM Spec => []FullInv
PROOF OMITTED

=============================================================================
