----------------------------- MODULE CountDown -----------------------------
(***************************************************************************)
(* Example of a counter that counts down from N to 0, together with a      *)
(* liveness proof showing that it will eventually reach 0.                 *)
(*                                                                         *)
(* Contributed by Andreas Recke.                                           *)
(***************************************************************************)
EXTENDS Naturals, TLC, TLAPS, NaturalsInduction

----
\* Input: N is the starting number for the countdown
CONSTANTS N

\* N must be a natural number
ASSUME NAssumption == N \in Nat

\* Variable i is the running countdown value
VARIABLES cnt

----
\* We define a set S which contains all possible values of the countdown counter
S == 0..N

----
\* Init: i starts at N
Init == cnt = N 

\* Next: if cnt is greater than 0, it will be count down by 1 in the next step
Next == cnt > 0 /\ cnt' = cnt-1

\* The complete spec. Important here is the fairness property. Otherwise, we
\* would not be able to proof that the count down may reach zero, because it
\* may infinitely stutter at a value larger than zero. 
Spec == Init /\ [][Next]_cnt /\ WF_cnt(Next)

----
\* Properties of the algorithm
Termination == <>(cnt=0)  \* count down reaches zero

NextEnabled == cnt > 0 \* for rewriting the ENABLED property to something simpler 

TypeInv == cnt \in S   
    \* the type correctness property is actually fundamental. 
    \* TLA+ values do not have a type, but proofs require it   

----
\* Theorems

\* this lemma ensures that the type of cnt is always correct
LEMMA TypeCorrectness == Spec => []TypeInv
\* From the correct input, ensured by NAssumption, Init leads to a correct type
<1>1. Init => TypeInv  
      BY NAssumption DEF Init, TypeInv, S
\* The Next transition, here encoded with the "[Next]_cnt" construct, leaves the 
\* TypeInv unchanged in the next state 
<1>2. TypeInv /\ [Next]_cnt => TypeInv'   
      BY NAssumption DEF TypeInv, Next, S
<1>3. QED 
    BY <1>1, <1>2, PTL DEF Spec  \* standard invariant reasoning

----
\* If the input constant N \in Nat, then we can prove that Spec leads to Termination (cnt=0)
\* We use the DownwardNatInduction rule which actually has the same goal as our algorithm:
\* start with a number N and prove that if fulfills a requirement P(N), i.e. <>cnt=N
\* Then just prove that for each n \in 1..N, where P(n) is fulfilled, the requirement P(n-1) 
\* is fulfilled, i.e. <>cnt=(n-1) 
\* This then proves, if cnt can be in 0..N that P(0) will be reached, i.e. <>cnt=0; which
\*  equals Termination 
THEOREM WillReachZero == Spec => Termination    
PROOF
\* The liveness proof uses an intermediate predicate for downward induction
\* Note that P(0) just expresses the assertion of the theorem.
<1> DEFINE P(m) == Spec => <>(cnt = m)  
<1> HIDE DEF P    
<1>2. P(0)  
    <2>1. P(N)  
\* Start condition - this is actually obvious. We show that initialization fulfills the first goal  
        BY PTL DEF P, Spec, Init
    <2>2. \A n \in 1..N : P(n) => P(n-1)  
\* prove: for all intermediate goals, the next goal will be reached
        <3>1. SUFFICES
                ASSUME NEW n \in 1 .. N 
                PROVE Spec /\ <>(cnt = n) => <>(cnt = n-1)   
\* Reformulation replacing the quantifier by a constant
\* Note that `Spec' remains in the conclusion so that PTL finds only "boxed" hypotheses in the QED step
            BY DEF P
        <3>2. (cnt=n) /\ [Next]_cnt => (cnt=n)' \/ (cnt=n-1)'   
             BY DEF Next
\* WF1 rule, step 1
        <3>3. (cnt=n) /\ <<Next>>_cnt => (cnt=n-1)'  
             BY DEF Next
\* WF1 rule, step 2
         <3>4. (cnt=n) => ENABLED <<Next>>_cnt  
             BY ExpandENABLED DEF Next
\* WF1 rule, step 3
        <3> QED
            BY <3>1, <3>2, <3>3, <3>4, PTL DEF Spec
\* Now we can conclude the WF1 rule reasoning      
    <2> QED
        BY NAssumption, <2>1, <2>2, DownwardNatInduction, Isa
\* taking the facts <2>1 and <2>2, downward natural induction works
<1> QED
    BY <1>2, PTL DEF P, Termination  
\* and finally, we can prove the overall goal to show that the spec/algorithm terminates 

=============================================================================
