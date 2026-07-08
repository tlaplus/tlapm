---- MODULE 17_ActionOperatorTest ----
EXTENDS TLAPS
VARIABLE x
Next == x' = x
THEOREM
  ASSUME [][Next]_x
  PROVE  [][UNCHANGED x]_x
PROOF
  <1> [Next]_x => UNCHANGED x BY ONLY DEF Next
  <1> QED BY PTL
====
