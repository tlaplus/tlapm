------------------------------- MODULE Basics -------------------------------
(***************************************************************************)
(* This tutorial aims to introduce beginners to the interactive proof system
   TLAPS which is part of the TLA+ project 
   (http://research.microsoft.com/en-us/um/people/lamport/tla/tla.html). 
   
   The tutorial is designed to be worked-through interactively in the TLA-toolbox.
   Before starting, you should make sure that you have the toolbox and the 
   proof manager installed correctly. (Check the toolbox page (http://research.microsoft.com/en-us/um/people/lamport/tla/toolbox.html)
   and the tlaps installation page (http://tla.msr-inria.inria.fr/tlaps/content/Download/Binaries.html) 
   for instructions.)
    
   This tutorial is desinged to be self-contained. It does not cover every 
   relevant detail. For further reading, please refer to the TLA+ hyperbook (http://research.microsoft.com/en-us/um/people/lamport/tla/hyperbook.html)
   and the TLA+2 Guide, which is the closest to a reference manual we have to offer (http://research.microsoft.com/en-us/um/people/lamport/tla/tla2-guide.pdf).
    

*)
(***************************************************************************)

(* In order to use the proof manager (PM), we need to import the TLAPS library: *)
EXTENDS TLAPS, Integers

----------------------------------------------------------------------------
(***************************************************************************
    GETTING STARTED
  
  This section introduces the user to the interactive proof structure of TLAPS.  
 ***************************************************************************)

(***************************************************************************    
  Let's start with a confidence-building excercise -- 
  let's prove something we know we can prove.
    
  There are different ways of doing that:
  The keywords "PROPOSITION", "LEMMA", "COROLLARY" and "THEOREM" open a proof.

  They are followed by the formula to be proved ("TRUE") in our case, 
  which can be given a name or not (compare the two lemmata below).

  To invoke the prover, place the cursor on the interesting line, right-click
  on it and then chose "Prove Step or Module".(1) Go ahead and invoke the PM
  on l.29 -- it should turn yellow, indicating that there is an unfinished 
  proof at this line.
  
  Now lets write our first proof: type "OBVIOUS" after or below the unproved
  lemma and invoke the PM again -- the lemma should turn green, indicating 
  that the PM has found and checked a valid proof.  
 ***************************************************************************)

LEMMA TRUE

(***************************************************************************
  TLAPS has two kinds of proofs: one-liners and hierarchical proofs. 
  (Compare [TLA2 Guide, Section 7.1] and [Hyperbook, 10.2].)  
  
  *One-liners* are either "OBVIOUS", "BY ...", or "BY ... DEF ... ".
  (Try substitution "OBVIOUS" above by "BY Isa", specifying Isabelle as the 
  backend-prover to be used.)
  
  *Hieararchical proofs* are structured into numbered levels, 
  each of which contains an arbitrary number of (named or un-named) steps, 
  and must be closed with a QED-step. (The parser will not accept a
  hieararchical proof with a level that is not closed by a QED-statement!)
  
  Each step (including the QED-step) takes its own proof, and the PM can be
  invoked on each individually. Below is a very simple example of a hieararchical 
  proof: Try invoking the PM on l.51 below (the QED-step should turn green), 
  then on l.49 (the lemma should turn yellow), then try proving the lemma.   
 ***************************************************************************)   
   
LEMMA Paula == TRUE
    <1>1 TRUE
    <1>q QED
        BY <1>1

-----------------------------------------------------------------------------
(***************************************************************************
  KNOWN AND USEABLE FACTS 
 
  The proofs above are a somewhat special case: usually we proof judgements 
  of the form Gamma |- f, where Gamma is some set of formulae and f is a 
  single one. This section concerns the structure and control of Gamma.
  (Compare [Hyperbook, Section 10.3] and [TLA2 Guide, Section 7.3].)
  
  There is a tension in our objectives for Gamma: 
    - on the one hand, we would like to have as much information as possible 
      in Gamma, because the more it contains, the more likely it contains 
      sufficient information to prove f;
    - on the other hand, the more information we hand to our backend provers
      the harder they have to work, the slower they become. 
      
  If we simply added everything we have proved to Gamma, then the proofs 
  would become slower and slower the longer a proof (or a module) grows, 
  until too many steps (or lemmata) make it impossible to prove anything; 
  that is a self-defeating situation for an interactive theorem prover. 
  
  To avoid it, we distinguish between the known facts, i.e. the maximum 
  Gamma, and the useable facts, i.e. the Gamma that is handed to the 
  background prover. The set of known facts grows monotonically. The set
  of useable facts is always a subset of the known facts and ideally 
  contains little more than the information required to prove the current goal.
  As TLAPS beginners we will spend considerable time on trying to control
  the useable facts within a proof.
  
  As a general rule of thumb, when a step is not given a name (e.g. <1>, <7>)
  itt assertion is added to the useable facts automatically;
  when a step is given a name (e.g. <1>A, <7>3), its assertion is not added to
  the useable facts automatically, but can be manually added or removed by 
  referring to the step by means of the keywords "USE", "HIDE", "BY" and "BY ONLY". 
  
  There are exceptions to there rules, if in doubt, consult the 
  descriptions of the commands in the [TLA2 Guide].  
  
  Let's try some things, to understand the problem and get to know some basic
  mechanisms of control. 
  **************************************************************************)

(***************************************************************************
  First we will need some constants to work with:
 ***************************************************************************)

CONSTANT a, b, c
ASSUME ConstantTypes ==    a \in Int
                        /\ b \in Int
                        /\ c \in Int
                 
(***************************************************************************
  Now consider the lemma le_trans, which is an instance of the transitivity 
  of the less-than relation. (The proof as structured below is a little strange, 
  since statement in terms of "=>" and the statement in <1>1 in terms of 
  "ASSUME-PROVE" are logically equivalent, but bear with us...)
  
  Invoke the PM on the mein lemma in l.119 and whatch what happens 
  (everything turns red, and on the right we get two interesting obligations).  
 ***************************************************************************)  
                 
LEMMA le_trans == a < b /\ b < c => a < c
    <1>1 ASSUME a < b,
                b < c
        PROVE  a < c
      OBVIOUS
    <1>q QED
      OBVIOUS

(***************************************************************************
  The interesting obligations show the current set of useable facts, under 
  the "ASSUME", and the current goal under the "PROVE". 
   
  Now modify the proof in some of the following ways and see what happens
  (in particular, observe what is added to the useable facts in the 
  interesting obligations):
  
  (a) Change "<1>1" to "<1>".
  
  (b) Replace both occurences of "OBVIOUS" with "BY <1>1".
    
  (c) (1) Replace the first "OBVIOUS" with "BY ConstantTypes".
      (2) Now add "<1>1" under the "BY".
      
  (d) (1) Add the line "<1>0 USE ConstantTypes" before "<1>1".  
      (2) Add the line "<1>  USE ConstantTypes" before "<1>1".
      (3) Now change the first "OBVIOUS" back to "BY <1>1".
      (4) Now add the line "<1> HIDE ConstantTypes" before "<1>1".

*Discuss.* 
----------------------------------------------------------------------------

TYPES: 
One message of the above is the importance of typing information.
The first obligation (the actual proof) is only solved, if the backend
prover (in this case the SMT solver) is explicitly told that a, b and c 
are integers. This information is required, to infer that "<" refers to 
the less-than relation on the integers. If a, b and c were something else,
"<" might refer to anything, in particular to a non-transitive relation.

*Hint:* 
When an obligation, that you think should be trivial, does not go through, 
always check whether you have all relevant type information in the useable
facts!    

 ***************************************************************************)
 
------------------------------------------------------------------------------
(***************************************************************************
    UNFOLDING DEFINITIONS
  
  Similar considerations as in the case of known vs useable facts apply to
  the question whether definitions should be unfolded or not. Therefore, 
  definitions are unfolded manually, by means of the keyword "DEF", which 
  can only occur under a "BY".
  
  To demonstrate, invoke the PM on the lemma LE_trans below, then replace
  "OBVIOUS" with "BY DEF LE"
    
 ***************************************************************************)

LE(x,y) == x < y

LEMMA LE_trans == ASSUME NEW x \in Int,
                         NEW y \in Int,
                         NEW z \in Int,
                         LE(x,y),
                         LE(y,z) 
                  PROVE  LE(x,z)
    OBVIOUS

-----------------------------------------------------------------------------
(***************************************************************************
    CALLING BACKEND SOLVERS
    
  The PM calls different backend solvers to discharge the proof obligations
  generated by a proof step. By default, it calls them in the following order:
      1. SMT
      2. Zenon
      3. Isabelle
  each with a timeout of 10 seconds. 

  The default order and timeout can be overwritten by means of "tactics",
  which are applied under a "BY": 
    - "SMT" will call an smt-solver only;
    - "Zenon" will call only Zenon;
    - "Isa" will call only Isa.
  
  Appending "T(<secs>)" to the tactic name will modify the timeout.    
     
  
  Each of these solvers is good at different things. 
  As a general rule of thumb, anything that involves arithmetic will require
  an SMT solver; anything that involves reasoning about several nested    
  quantifiers  will require Zenon or Isabelle.  
  
  To get an idea, try the following theorem, by Isa, by Zenon, and by SMT:
 ***************************************************************************)

LEMMA syntax == ASSUME NEW U \in (Int \X Int),
                       NEW p \in Int,
                       <<p, p-1>> \in U
                PROVE <<p,p-2+1>> \in U
    BY Isa
    
-----------------------------------------------------------------------------
(***************************************************************************
    SAFETY PROOFS -- PROVING BOXES
    
 Safety properties often state things like "In this system, it is always the case, that ...".
 Formally, a safety theorem often takes the shape:      Spec => []Safety
            
 This section introduces the reader to the basics of proving such a statement.
   
   
 To demonstrate, take a very simple simple specification, the binary clock 
 (compare [Chapter 2,Hyperbook]):    
 ***************************************************************************)

VARIABLE B

TypeOK == B \in {0,1}

Init == (B=0) \/ (B=1)

Next ==  IF B = 0 THEN  B' = 1 ELSE  B' = 0

Spec == Init /\ [][Next]_<<B>>

(***************************************************************************
 Say we want to prove that B is always either 0 or 1 (i.e. []TypeOK).
 
 Now the question is: How does one prove a box?
 
 The intuition is: 
 to prove "always A", 
        prove "initially A", 
        and   "if A now, then A in the next state".
    
 
 The relevant rule is:     Init => A          A /\ [Next]_vars => A'
                         --------------------------------------------
                                 Init /\ [][Next]_vars => []A
                           
 As a TLA+ proof, it looks like this:
 ***************************************************************************)

THEOREM Spec => []TypeOK
<1>1 Init => TypeOK

<1>2 [Next]_<<B>> /\ TypeOK => TypeOK'

<1>q QED
    BY  <1>1, <1>2, LS4 DEF Spec 

(***************************************************************************
 As an exercise, finish the proof above.
 
 *Hint:*
    We have not talked about the [A]_vars - construct (read "square A sub vars").
    [A]_vars is defined as "A \/ UNCHANGED vars" (see [Hyperbook, Section 6.7.2]). 
    
    The inner strucutre of the second step should therefore look like this:
        <2>1 CASE Next
        <2>2 CASE UNCHANGED <<B>>
        <2>q QED
             BY <2>1, <2>2 
 ***************************************************************************)
 
 (**************************************************************************
    BOXED vs NON-BOXED CONTEXT
 
 Since Spec implies both Init and [][Next]_<<B>>, one may think that the two 
 steps of the proof could also be:
 
 <1>1 Spec => TypeOK
 <1>2 Spec /\ TypeOK => TypeOK'    
 
 Change the proof and see what happens. You should find that the first step 
 is fine, but the second breaks the proof. Why is that? 
 
 Remember that the role the second step plays in the proof is intuitively:
    "always, if A is true now, then A is true in the next step". 

 We have no guarantee that Init is true beyond the initial state; therefore 
 we cannot use it as an assumption in this situation. The rule is, that 
 any formula F we want to use as an assumption this step, has to occur boxed,
 i.e. as []F, in Spec.  
  **************************************************************************)


(***************************************************************************
    NEXT: EUCLID
    
 This covers the basics of the TLA PM and puts us in a position to try and 
 prove some interesting things. The reader should go next to the file 
 exercise_Euclid.tla.    
    
 ***************************************************************************)


-----------------------------------------------------------------------------
(***************************************************************************
(1) The keyboard shortcut Ctrl-g Ctrl-g is not 100% stable. It appears that 
    to use it one needs to: 
        1. make a change
        2. save (Ctrl-s)
        3. invoke the prover with Ctrl-g Ctrl-g

 ***************************************************************************)
=============================================================================
\* Modification History
\* Last modified Wed Feb 05 14:35:20 CET 2014 by jael
\* Last modified Tue Feb 04 13:19:05 CET 2014 by merz
\* Created Tue Jan 28 09:49:11 CET 2014 by jael
