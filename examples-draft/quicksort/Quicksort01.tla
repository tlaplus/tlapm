----------------------------- MODULE Quicksort01 -----------------------------
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

THEOREM Spec => []Safety
(* OK, how does one proof anything? -> go to online tutorial to look up basic proof structure 

    actually, I was hoping for something like "A TLA+ Proof looks like this:... 
    a little higher level than the "A simple proof" section on the TLA+ Proos System website
-------------------------------------------------------------------------------------------
 
 attempt 1: 
    Let's just try writing OBVIOUS and see what happens...

 notes: 
    - it took Damien to explain to me that I can't write anything under the `=========================` 
++++++++++ 
OBVIOUS 
*)
 
 
(*    
  attempt 2:
    Attempt 1 didn't get us far, we'll have to be more sophisticated than that, so I'm scrolling down the online tutorial 
  
 
     OK, it took me  a while to find the "the general form af a BY proof is : ...." on the 
     website, but now I found it, so I'll use it... 
    
   notes:
   - I find it un-intuitive, that I can't unfold WF_(vars) or WF like Spec etc...    
+++++++++++
BY ConstantAssump DEF Spec, Safety
 *)

(*  attempt 3:
    Attempt 2 got me in an interactive mindset: I can see that I can interact with the proof state by looking and changing these obligations
    I played around with adding "Next" and "Init" to the list after "DEF". 
    
    But logically it didn't get me anywhere, so I'll try something else: 
        
    Ok, now I'm on the "Hierarchical proofs" section on the website, and it seems to tell me how to do an 
    an implication elimination, which is a relief. It seems to be done by "suffices [..] assume [..] proof"
    
    notes:
    - I started out with the following code:
    <1> SUFFICES ASSUME Speck
                 PROVE []Safety
       
      I got a cryptic error message, it took Damien to explain that every step of a hierarchical proof needs to be closed by a "QED"-step with the same level
      
      I think the underlying problem there may be that in the online tutorial there are partial bits of code, which when copied and pasted give syntax errors.
      
    - Damien also pointed out I should be using the hyperbook ... That is referenced in the preamble to the online tutorial, but I skipped the preamble.
        I think there is a deeper problem there: all the documentation is very example-driven and very holistic in the sense that there is a lot of text and a lot of explaining. 
        I'm in a goal-oriented mindest: I have a theorem, I want to prove it. What I'm really looking for are answers to 
        questions like "How do I do implication elimination?" "How do I prove a box?" "What does the most basic syntactically correct hierarchical proof look like?", etc.
        So some sort of documentation that can be accesses in a demand-driven way, or a cheat-sheet with the most basic proof structures.
 
    - The way "QED" steps work is not intuitive, at least not yet... 
    
     *)
<1> SUFFICES ASSUME Spec
             PROVE []Safety
<1>1 []Safety                
<1> QED  
    BY <1>1, LS4
    
   (* Side Notes:
    - it is annoying that the parser errors don't wrap around lines and I don't seem to be able to sort windows in the toolbox, so I can have them below the obligations... *)




=============================================================================

