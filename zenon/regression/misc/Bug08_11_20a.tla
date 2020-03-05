-------------------------- MODULE Bug08_11_20a --------------------------- 

(***************************************************************************)
(* Something weird is going on here.  Go down to the proof at the end of   *)
(* the file and observe that it's not deducing <3>4 from <3>2 and <3>3.    *)
(* It appears that the problem isn't with that deduction, since the        *)
(* following works fine.                                                   *)
(*                                                                         *)
(*    f == {}                                                              *)
(*    g == {}                                                              *)
(*                                                                         *)
(*    THEOREM ASSUME g = [f EXCEPT ![0] = 0],                              *)
(*                   DOMAIN f = {0,1}                                      *)
(*            PROVE  g[1] = f[1]                                           *)
(*    OBVIOUS                                                              *)
(*                                                                         *)
(* It appears that it's not deducing that step <3>2 follows from step      *)
(* <3>2.                                                                   *)
(***************************************************************************)

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

AXIOM Arith == 0 # 1

\* BEGIN TRANSLATION
CONSTANTS flag, turn, pc, flag_p, turn_p, pc_p


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



THEOREM Inductive == Strings /\ TypeOK /\ I /\ Next => I_p
      <3>2. pc_p = [pc EXCEPT ![0] = "a1"]
      <3>3. DOMAIN pc = {0, 1}

(***************************************************************************)
(*       HERE'S THE STEP THAT'S FAILING                                    *)
(***************************************************************************)
      <3>4. pc_p[1] = pc[1]
BY <3>2, <3>3, Arith
      <3>5. QED
=============================================================================
