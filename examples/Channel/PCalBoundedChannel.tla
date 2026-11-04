------------------------- MODULE PCalBoundedChannel -------------------------
EXTENDS Integers, Sequences, TLAPS

CONSTANT Msg, N

ASSUME NAssump == N \in Nat \ {0}
USE NAssump 

(***************************************************************************
--algorithm BChan {
   variable ch = << >>;
   process (Send = "S")
    { s: while (TRUE)
          { await Len(ch) # N ;
            with (v \in Msg) { ch := Append(ch, v) }
          }
    }
   (*fair*) process (Rcv = "R")
    { r: while (TRUE)
          { await Len(ch) # 0 ;
            ch := Tail(ch)
          }
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLE ch

vars == << ch >>

ProcSet == {"S"} \cup {"R"}

Init == (* Global variables *)
        /\ ch = << >>

Send == /\ Len(ch) # N
        /\ \E v \in Msg:
             ch' = Append(ch, v)

Rcv == /\ Len(ch) # 0
       /\ ch' = Tail(ch)

Next == Send \/ Rcv

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

TypeOK == ch \in Seq(Msg)

Inv == /\ TypeOK
       /\ Len(ch) =< N

THEOREM Invariant == Spec => []Inv 
<1>1. Init => Inv 
  BY DEF Init, Inv, TypeOK 
<1>2. Inv /\ [Next]_vars => Inv'
  BY DEF Inv, TypeOK, Next, Send, Rcv, vars 
<1>. QED  BY <1>1, <1>2, PTL DEF Spec 

=============================================================================
\* Created Sun Apr 17 11:40:12 PDT 2011 by lamport
