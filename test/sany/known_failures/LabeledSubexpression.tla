The SANY XML Exporter does not give enough information to convert labeled
subexpressions. Seen in the following tlaplus/examples specs:
 - specifications/ewd840/EWD840_proof.tla
 - specifications/byzpaxos/PConProof.tla
---- MODULE LabeledSubexpression ----
Inv == /\ P1 :: TRUE
       /\ P2 :: TRUE
THEOREM Inv!P1
PROOF BY DEF Inv
====
