---- MODULE naive_debug ----
\* EXTENDS TLAPS
CONSTANT Nodes
CONSTANT Values
ASSUME \E n \in Nodes : TRUE
CONSTANT AAA

VARIABLE proc
VARIABLE msgs
VARIABLE xxxx
vars == <<proc, msgs>>

Msgs == UNION {
    [t: {"C_SEND"}, v: Values, dst : Nodes],
    [t: {"B_CAST"}, v: Values, dst : Nodes, src : Nodes]
}

TypeOK ==
    /\ proc \in [Nodes -> Values]
    /\ msgs \in SUBSET Msgs

-------------------------
\* Actions

SendAnswer ==
    \E v \in Values, n \in Nodes:
        /\ msgs' = msgs \cup {[t |-> "C_SEND", v |-> v, dst |-> n]}
        /\ UNCHANGED proc

XXX == TRUE

RecvAnswer(n) ==
    \E m \in msgs :
        /\ m.t = "C_SEND"
        /\ m.dst = n
        /\ proc' = [proc EXCEPT ![n] = m.v ]
        /\ msgs' = msgs \cup [t: {"B_CAST"}, v: {m.v}, dst : Nodes \ {n}, src : {n}]


-------------------------
\* Spec
Init ==
    /\ \E v \in Values : proc = [ n \in Nodes |-> v ]  \* \in  [Nodes -> {v}]
    /\ msgs = {}
Next ==
    \/ SendAnswer
    \/ \E n \in Nodes : RecvAnswer(n)

Spec == Init /\ [][Next]_vars

-------------------------
\* Properties

THEOREM Spec => []TypeOK
    <1>1. Init => TypeOK
      <2> HAVE Init
      <2>1. proc \in [Nodes -> Values] BY DEFS TypeOK, Init
      <2>2. msgs \in SUBSET Msgs BY DEFS TypeOK, Init, Msgs
      <2> QED BY <2>1, <2>2 DEF TypeOK

    <1>2. (TypeOK /\ [Next]_vars) => TypeOK'
      <2>1. HAVE TypeOK /\ [Next]_vars
      <2>2. TypeOK BY <2>1
      <2>3. [Next]_vars BY <2>1
      <2>4. CASE Next BY <2>2, <2>3, <2>4
      <2>5. CASE UNCHANGED vars BY <2>2, <2>3, <2>5
      <2> QED BY <2>4, <2>5

    \* <1>z. \A x \in Init : TypeOK
    \*   <2> TAKE x \in TypeOK
    \*   <2> QED 
    <1>q. QED BY <1>1, <1>2 (*, PTL *) DEF Spec
====
