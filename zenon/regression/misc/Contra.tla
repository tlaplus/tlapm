---- MODULE Contra ----

CONSTANT A

THEOREM A => ~ ~ A
PROOF
  <1>. HAVE A
  <1>. ASSUME ~ A
       PROVE FALSE
       <2>. A /\ ~ A OBVIOUS
       <2>. QED OBVIOUS
  <1>. QED OBVIOUS


====================
