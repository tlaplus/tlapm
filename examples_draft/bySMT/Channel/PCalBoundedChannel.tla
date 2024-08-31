------------------------- MODULE PCalBoundedChannel -------------------------
EXTENDS Integers, Sequences

CONSTANT Msg, N

ASSUME N \in Nat \ {0}

(***************************************************************************
--algorithm BChan {
   variable ch = << >>;
   process (Send = "S")
    { s: while (TRUE)
          { await Len(ch) # N ;
            with (v \in Msg) { ch := Append(ch, v) }
          }
    }
   fair process (Rcv = "R")
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

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Rcv)

\* END TRANSLATION

TypeOK == ch \in Seq(Msg)

Inv == /\ TypeOK
       /\ Len(ch) =< N
=============================================================================
\* Modification History
\* Last modified Fri Aug 05 17:13:34 PDT 2011 by lamport
\* Created Sun Apr 17 11:40:12 PDT 2011 by lamport
