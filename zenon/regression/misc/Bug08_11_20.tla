------------------------------ MODULE Bug08_11_20 -------------------------- 

Not(i) == IF i = 0 THEN 1 ELSE 0

Strings == 
/\ "a0" # "a1"
/\ "a0" # "a2"
/\ "a0" # "a3"
/\ "a0" # "cs"
/\ "a0" # "a4"
/\ "a1" # "a2"
/\ "a1" # "a3"
/\ "a1" # "cs"
/\ "a1" # "a4"
/\ "a2" # "a3"
/\ "a2" # "cs"
/\ "a2" # "a4"
/\ "a3" # "cs"
/\ "a3" # "a4"
/\ "cs" # "a4"

(*******

--algorithm Peterson {
   variables flag = [i \in {0, 1} |-> FALSE], turn = 0;
   process (proc \in {0,1}) {
     a0: while (TRUE) { 
     a1:   flag[self] := TRUE; 
     a2:   turn := Not(self);       
     a3:   while (flag[Not(self)] /\ turn = Not(self)) {
             skip };
     cs:   skip;  \* critical section   
     a4:   flag[self] := FALSE;            
     } \* end while
    } \* end process
  }
********)

\* BEGIN TRANSLATION
CONSTANTS flag, turn, pc, flag_p, turn_p, pc_p

vars == << flag, turn, pc >>

ProcSet == ({0,1})

Init == (* Global variables *)
        /\ flag = [i \in {0, 1} |-> FALSE]
        /\ turn = 0
        /\ pc = [self \in ProcSet |-> "a0"]

a0(self) == /\ pc[self] = "a0"
            /\ pc_p = [pc EXCEPT ![self] = "a1"]
            /\ flag_p = flag
            /\ turn_p = turn

a1(self) == /\ pc[self] = "a1"
            /\ flag_p = [flag EXCEPT ![self] = TRUE]
            /\ pc_p = [pc EXCEPT ![self] = "a2"]
            /\ turn_p = turn

a2(self) == /\ pc[self] = "a2"
            /\ turn_p = Not(self)
            /\ pc_p = [pc EXCEPT ![self] = "a3"]
            /\ flag_p = flag

a3(self) == /\ pc[self] = "a3"
            /\ IF flag[Not(self)] /\ turn = Not(self)
                  THEN /\ TRUE
                       /\ pc_p = [pc EXCEPT ![self] = "a3"]
                  ELSE /\ pc_p = [pc EXCEPT ![self] = "cs"]
            /\ flag_p = flag
            /\ turn_p = turn


cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc_p = [pc EXCEPT ![self] = "a4"]
            /\ flag_p = flag
            /\ turn_p = turn


a4(self) == /\ pc[self] = "a4"
            /\ flag_p = [flag EXCEPT ![self] = FALSE]
            /\ pc_p = [pc EXCEPT ![self] = "a0"]
            /\ turn_p = turn

proc(self) == a0(self) \/ a1(self) \/ a2(self) \/ a3(self) \/ cs(self)
                 \/ a4(self)

Next == (\E self \in {0,1}: proc(self))
\*           \/ (* Disjunct to prevent deadlock on termination *)
\*              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars \*  /\ \A self \in {0,1}: WF_vars(proc(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

Safe == \E i \in {0, 1} : pc[i] # "cs"

Live == \A i \in {0, 1} : []<>(pc[i] = "cs")
-----------------------------------------------------------------------------
\* The proof

TypeOK == /\ pc \in [{0,1} -> {"a0", "a1", "a2", "a3", "cs", "a4"}]
          /\ turn \in {0, 1}
          /\ flag \in [{0,1} -> BOOLEAN]

II(i) ==
       /\ (pc[i] \in {"a2", "a3", "cs", "a4"} ) => flag[i]
            
       /\ (pc[i] \in {"cs", "a4"}) => /\ pc[Not(i)] \notin {"cs", "a4"}
                                      /\ (pc[Not(i)] = "a3") => (turn = i)

I == \A i \in {0, 1} : II(i)


TypeOK_p == /\ pc_p \in [{0,1} -> {"a0", "a1", "a2", "a3", "cs", "a4"}]
            /\ turn_p \in {0, 1}
            /\ flag_p \in [{0,1} -> BOOLEAN]



II_p(i) ==  /\ (pc_p[i] \in {"a2", "a3", "cs", "a4"} ) => flag_p[i]
            
            /\ (pc_p[i] \in {"cs", "a4"}) => 
                    /\ pc_p[Not(i)] \notin {"cs", "a4"}
                    /\ (pc_p[Not(i)] = "a3") => (turn_p = i)


I_p == \A i \in {0, 1} : II_p(i)

ISpec == (TypeOK /\ I) /\ [][Next]_vars


THEOREM Inductive == Strings /\ TypeOK /\ I /\ Next => I_p
\*  <1>  USE DEF Strings
  <1>1. ASSUME Strings,
               TypeOK, 
               I,
               NEW i \in {0,1},
               proc(i) 
        PROVE  I_p

    <2>1. ASSUME NEW j \in {0, 1}
          PROVE  II_p(j)

    <2>2. QED
      BY <2>1 DEF I_p
   <1>2. QED
\***  BY <1>1 DEF Next   \* Proved 20 Nov 08
=============================================================================
