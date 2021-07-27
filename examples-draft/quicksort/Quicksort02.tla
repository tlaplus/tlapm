----------------------------- MODULE Quicksort02 -----------------------------
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
Inv == TypeOK /\ Safety


THEOREM Spec => []Safety


(* attempt 5:
    Right, how does one proof a box? 
      
    Hypterbook 11.1 is very useful! it's a pity that it isn't self contained: I don't know what `Inv' is...
        I'll just try adding it as an undefined symbol and see what happens...  
         
<1>1 Init => Inv
<1>2 Inv /\ [Next]_vars => Inv'
<1>3 Inv => Safety

<1>4 QED  
        *)
    
(* attempt 6:
    right, that didn't work: now I'll have to go chase references in the hyperbook... 

    reading Sec. 4.9.1 is helpful, let's try find an inductive invariant...
    
    It seems like Safety itself is a reasonable working hypothesis for an invariant for now... 
 Let's try that plus TypeOK -- 
    can I define things in the middle of proofs?
        Inv == /\ TypeOK /\ Safety
    apparently not...  

    Ok, now it's just under the definition of 'Safety'.    
    Now when I go C-g C-g everything is yellow, but I get no interesting obligations... ?

    I'll try and get the QED green first... 
    
+++++++++++++++++++     
<1>1 Init => Inv
<1>2 Inv /\ [Next]_vars => Inv'
<1>3 Inv => Safety
<1>4 QED  
    BY  LS4, <1>1, <1>2, <1>3  DEF Inv, Spec (* AHA!! my first very own green `QED' ! celebratory cup of tea! *)
   
( attempt 7: 
    now for the steps in between:   
    
    <1>1: 
    I'm getting a syntax error for this: why?!?     
++++++++++++++++++
<1>1 Init => Inv
    PROOF
    <2>1 ASSUME Init
         PROVE Inv
    <2>2 BY <2>1 DEF Init, Inv, TypeOK, Safety
         
<1>2 Inv /\ [Next]_vars => Inv'
<1>3 Inv => Safety

<1>4 QED  
    BY  LS4, <1>1, <1>2, <1>3  DEF Inv, Spec 
++++++++++++++++++++ 
*)
         
         
(* attempt 8: 
    aha, always put the `QED' !  

          
    *)

<1>1 Init => Inv
    PROOF
    <2>1 ASSUME Init
         PROVE   U # {}
        BY <2>1 DEF Init
    (* getting the syntax right here took me a long time: I'm not sure what the `BY' is proving: 
        If it's the `ASSUME-PROVE' then why does it need not be tols to use <2>1 ? 
        If its something else, then why does putting a label like <2>2 in front of it result in a syntax error? *)
     <2>2 SUFFICES (Init => U # {}) /\ (Init => TypeOK)
        BY DEF Inv, Safety, TypeOK
     <2>3 Init => U # {}
        BY DEF Init
      <2>4 Init => TypeOK
        BY Z3, ConstantAssump DEF Init, TypeOK, ConstantAssump
      <2> QED
        BY <2>2, <2>3, <2>4 
    (* The `QED' referrs to <1>1 ? Why is it still red? *)    
                      
<1>2 Inv /\ [Next]_vars => Inv'
    PROOF
    <2>1 SUFFICES (TypeOK /\ [Next]_vars => TypeOK') /\ (Inv /\ [Next]_vars => Safety')
      BY DEF Inv
    <2>2 ASSUME TypeOK, [Next]_vars
         PROVE TypeOK'
    (* right-clicking on this and then clicking `Decompose Proof' gives me an error message 
        "Spec status must be `parsed' to execute this command" -- but my spec status is `parsed' !!? *)


        <3>1 SUFFICES (A  \in  [1 .. N -> Int] /\ [Next]_vars => A' \in [1..N -> Int]) 
                   /\ ( (U  \in  SUBSET ((1 .. N)  \X  (1 .. N))) /\ [Next]_vars =>  U'  \in  SUBSET ((1 .. N)  \X  (1 .. N)))
           BY <3>1 DEF TypeOK 
           (* It seems to me that this is just reordering the conjunctions (conjunction elimination + weakening on the left-side and conjunction introduction on the right)?
                why doesn't it work? *)
        <3> QED 
        
    <2> QED
    BY <2>1 DEF Inv
<1>3 Inv => Safety
    <2> QED
      BY DEF Inv
        
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
   
   *)


=============================================================================
    
