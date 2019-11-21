----------------------------- MODULE Quicksort04 -----------------------------
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

(* Ok, I think I got the hang of basic proof structures, 
    now let's do some logic...
    
    
*)

THEOREM Spec => []Safety
<1>1 Init => Inv
    PROOF
    <2>1 ASSUME Init
         PROVE   U # {}
        BY <2>1 DEF Init
     <2>2 SUFFICES (Init => U # {}) /\ (Init => TypeOK)
        BY DEF Inv, Safety, TypeOK
     <2>3 Init => U # {}
        BY DEF Init
      <2>4 Init => TypeOK
        BY Z3, ConstantAssump DEF Init, TypeOK, ConstantAssump
      <2> QED
        BY <2>2, <2>3, <2>4 
                      
<1>2 Inv /\ [Next]_vars => Inv'
    <2>1 SUFFICES (TypeOK /\ [Next]_vars => TypeOK') /\ (Inv /\ [Next]_vars => Safety')
      BY DEF Inv
    <2>2 ASSUME TypeOK, [Next]_vars
         PROVE TypeOK'
      <3>1. CASE Next (* here I'm trying to decompose and it just quietly does nothing... *)
        <4>1 SUFFICES ASSUME TypeOK, 
                            U  #  {}, 
                            \E b \in 1 .. N, t \in 1 .. N : 
                                /\ <<b, t>>  \in  U
                                /\ IF b  #  t
                                    THEN \E p \in b .. t  -  1 :
                                        /\ A'  \in  Partitions(A, p, b, t)
                                        /\ U' =  (U  \  {<<b, t>>})  \union {<<b, p>>, <<p  +  1, t>>}
                                    ELSE /\ U'  =  U  \  {<<b, t>>}
                                         /\ A'  =  A
                       PROVE TypeOK'
          BY <2>2, <3>1 DEF Next
          <4>2 ASSUME TypeOK, 
                      U  #  {}, 
                     NEW b \in 1 .. N, 
                     NEW t \in 1 .. N,  
                            /\ <<b, t>>  \in  U
                            /\ IF b  #  t
                               THEN \E p \in b .. t  -  1 :
                                    /\ A'  \in  Partitions(A, p, b, t)
                                    /\ U' =  (U  \  {<<b, t>>})  \union {<<b, p>>, <<p  +  1, t>>}
                               ELSE /\ U'  =  U  \  {<<b, t>>}
                                    /\ A'  =  A
                PROVE TypeOK'
                <5>1 CASE b # t
                    <6>1 SUFFICES ASSUME    TypeOK, 
                                            U # {},
                                            \E p \in b .. t  -  1 :
                                                /\ A'  \in  Partitions(A, p, b, t)
                                                /\ U' =  (U  \  {<<b, t>>})  \union {<<b, p>>, <<p  +  1, t>>}
                                  PROVE TypeOK'
                          BY <4>2, <5>1 
                    <6>2 ASSUME TypeOK, U # {},
                                NEW p \in b .. t  -  1, 
                                    /\ A'  \in  Partitions(A, p, b, t)
                                    /\ U' =  (U  \  {<<b, t>>})  \union {<<b, p>>, <<p  +  1, t>>}
                         PROVE TypeOK'   
                         <7>1. (A \in [1..N -> Int])'
                            BY Z3, <6>2 DEF TypeOK, Partitions, PermsOf
                         <7>2. (U \in SUBSET ((1..N) \X (1..N)))'
                            BY Z3, <6>2 DEF TypeOK
                         <7>q QED
                         (* Why doesn't Z3 prove this?? Surely I don't have to do anything about this? *)
                            BY <6>2, <7>1, <7>2
                    <6>q QED
                        BY <5>1, <6>1, <6>2
                <5>2 CASE b = t
                    <6>1 SUFFICES ASSUME TypeOK, U # {}, b = t, 
                                         U' = U \ {<<b, t>>},
                                         A' = A
                                  PROVE TypeOK'
                            BY <4>2, <5>2
                    <6>2 ASSUME TypeOK, U # {}, b = t,
                                         U' = U \ {<<b, t>>},
                                         A' = A
                         PROVE TypeOK'
                      <7>1. (A \in [1..N -> Int])'
                        BY Z3, <6>2 DEF TypeOK
                      <7>2. (U \in SUBSET ((1..N) \X (1..N)))'
                        BY Z3, <6>2 DEF TypeOK
                      <7>q QED
                        BY <7>1, <7>2 DEF TypeOK
                    <6>q QED
                        BY <6>1, <6>2 
                <5>q QED         
                    BY <4>2, <5>1, <5>2
        <4>q QED
        BY <4>1, <4>2 DEF Next
      
      <3>2. CASE UNCHANGED vars
        <4>q QED
            BY  <2>2, <3>2 DEF TypeOK, vars
      <3>q QED
        BY <3>1, <3>2, <2>2
  
    <2>3 ASSUME Inv, [Next]_vars
         PROVE Safety'
         <3>1 CASE UNCHANGED vars
            <4>q QED
                BY <3>1, <2>3 DEF Inv, vars, Safety
         <3>2 CASE Next
             <4>1 SUFFICES ASSUME Inv,
                                  U  #  {}, 
                                  \E b \in 1 .. N, t \in 1 .. N : 
                                  /\ <<b, t>>  \in  U
                                    /\ IF b  #  t
                                        THEN \E p \in b .. t  -  1 :
                                             /\ A'  \in  Partitions(A, p, b, t)
                                             /\ U' =  (U  \  {<<b, t>>})  \union {<<b, p>>, <<p  +  1, t>>}
                                        ELSE /\ U'  =  U  \  {<<b, t>>}
                                             /\ A'  =  A
                       PROVE Safety'
                  BY <2>3, <3>2 DEF Next, Inv 
            <4>2 ASSUME Inv, 
                        U  #  {}, 
                        NEW b \in 1 .. N, 
                        NEW t \in 1 .. N,  
                                /\ <<b, t>>  \in  U
                                /\ IF b  #  t
                                    THEN \E p \in b .. t  -  1 :
                                         /\ A'  \in  Partitions(A, p, b, t)
                                         /\ U' =  (U  \  {<<b, t>>})  \union {<<b, p>>, <<p  +  1, t>>}
                                    ELSE /\ U'  =  U  \  {<<b, t>>}
                                         /\ A'  =  A
                PROVE Safety'
                <5>1 CASE b # t
(*                    <6>1 SUFFICES ASSUME    TypeOK, 
                                            U # {},
                                            \E p \in b .. t  -  1 :
                                                /\ A'  \in  Partitions(A, p, b, t)
                                                /\ U' =  (U  \  {<<b, t>>})  \union {<<b, p>>, <<p  +  1, t>>}
                                  PROVE TypeOK'
                          BY <4>2, <5>1 
*)

                <5>2 CASE b = t
                     <6>1 SUFFICES ASSUME Safety, 
                                          U # {},
                                          U' = U \ {<<b, t>>},
                                          A' = A
                                   PROVE  Safety'
                         BY <4>2, <5>2 DEF Next, Safety
                     
                     <6>2 ASSUME Safety, 
                                 U # {},
                                 U' = U \ {<<b, t>>},
                                 A' = A
                          PROVE  Safety'
                          <7>1 SUFFICES 
                                 /\ ( (A' = A /\ IsSorted(A)) => IsSorted(A') )  
                                 /\ ( ( /\ U # {} 
                                        /\ U' = U \ {<<b, t>>}
                                        /\ A' = A )                                          
                                       =>  (U' = {} => A' \in PermsOf(A0) /\ IsSorted(A') )
                                    ) 
                              BY <6>2  DEF Safety                  
                              
                          <7>2 (A' = A /\ IsSorted(A)) => IsSorted(A')
                            OBVIOUS
                          <7>3 ( /\ U # {} 
                                 /\ U' = U \ {<<b, t>>}
                                 /\ A' = A )                                          
                                =>  (U' = {} => A' \in PermsOf(A0) /\ IsSorted(A') )
                                PROOF                             
                                <8>1 CASE U' = {}
                                <8>2 CASE U' # {}   
                                    OBVIOUS (* how is this not obvious ??? *)
                                <8>q QED
                                    BY <8>1, <8>2 (* putting `<7>3' here give an error "<7>3 used in its own proof..." usually the QED needs to mention its object under a BY?? *)
                          <7>q QED
                            BY <6>2, <7>1, <7>2, <7>3 
                      <6>q QED
                        BY <5>2, <6>1, <6>2  
                <5>q QED  
            <4>q QED
                BY <3>2, <2>3 DEF Inv, Safety, Next 
        <3>q QED
            BY <3>1, <3>2, <2>3
    <2>q QED
    BY <2>1, <2>2, <2>3 DEF Inv
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
   
  - The fact that the prover sometimes doesn't launch on C-g C-g is very annoying... 
  
  - Highlighting matching parantheses would be helpful...  
  
  - For some reason my touchpad's righ mouse button doesn't open the menu;
    given that the key shortcuts are very unstable, it would be good to 
    be able to get at things from the main menu
    
  - It would be useful to be able to `print' definitions like Safety -- scolling back and forth in the middle of a long proof takes time... 
   *)


=============================================================================
    