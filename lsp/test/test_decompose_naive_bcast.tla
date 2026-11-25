\* cspell:words BCAST
---- MODULE test_decompose_naive_bcast ----
CONSTANT Nodes
CONSTANT Values
ASSUME Assm == \E n \in Nodes : TRUE

VARIABLE proc
VARIABLE msgs
vars == <<proc, msgs>>

Msgs == UNION {
    [t: {"INPUT"}, v: Values, dst : Nodes],
    [t: {"BCAST"}, v: Values, dst : Nodes, src : Nodes]
}

TypeOK ==
    /\ proc \in [Nodes -> Values]
    /\ msgs \in SUBSET Msgs

-------------------------
\* Actions

SendInput ==
    \E v \in Values, n \in Nodes:
        /\ msgs' = msgs \cup {[t |-> "INPUT", v |-> v, dst |-> n]}
        /\ UNCHANGED proc

RecvInput(n) ==
    \E m \in msgs :
        /\ m.t = "INPUT"
        /\ m.dst = n
        /\ proc' = [proc EXCEPT ![n] = m.v ]
        /\ msgs' = msgs \cup [t: {"BCAST"}, v: {m.v}, dst : Nodes \ {n}, src : {n}]

RecvBCast(n) ==
    \E m \in msgs :
        /\ m.t = "BCAST"
        /\ m.dst = n
        /\ proc' = [proc EXCEPT ![n] = m.v ]
        /\ UNCHANGED msgs

-------------------------
\* Spec

Init ==
    /\ \E v \in Values : proc \in [Nodes -> {v}]
    /\ msgs = {}
Next ==
    \/ SendInput
    \/ \E n \in Nodes :
        \/ RecvInput(n)
        \/ RecvBCast(n)

Spec == Init /\ [][Next]_vars

-------------------------
\* Properties

INSTANCE TLAPS

\* A minimal(ish) version.
THEOREM Spec => []TypeOK
    <1> USE DEF TypeOK, Msgs, vars
    <1>1. Init => TypeOK BY DEFS Init
    <1>2. TypeOK /\ [Next]_vars => TypeOK'
      <2> QED BY DEFS Next, RecvBCast, RecvInput, SendInput
    <1>q. QED BY <1>1, <1>2, PTL DEF Spec

\* The same, just more decomposed.
THEOREM Spec => []TypeOK
    <1>1. Init => TypeOK BY DEFS Init, TypeOK, Msgs
    <1>2. TypeOK /\ [Next]_vars => TypeOK'
      <2>1. HAVE TypeOK /\ [Next]_vars
      <2>2. TypeOK BY <2>1
      <2>3. [Next]_vars BY <2>1
      <2>4. CASE SendInput BY <2>2, <2>3, <2>4 DEFS Next, SendInput, TypeOK, Msgs
      <2>5. CASE \E n \in Nodes : \/ RecvInput(n)
                                  \/ RecvBCast(n)
        <3>1. PICK n \in Nodes : \/ RecvInput(n)
                                 \/ RecvBCast(n)
              BY <2>2, <2>3, <2>5 DEF Next
        <3>2. CASE RecvInput(n) BY <3>2, <2>2 DEFS Next, RecvInput, TypeOK, Msgs
        <3>3. CASE RecvBCast(n) BY <3>3, <2>2 DEFS Next, RecvBCast, TypeOK, Msgs
        <3> QED BY <3>1, <3>2, <3>3 DEF Next
      <2>6. CASE UNCHANGED vars BY <2>6, <2>2 DEFS vars, TypeOK, Msgs
      <2> QED BY <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next
    <1>q. QED BY <1>1, <1>2, PTL DEF Spec

====
