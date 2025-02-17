---- MODULE nat_comparison_soundness_gh200 ----
EXTENDS TLAPS, Naturals

THEOREM SoundnessError == FALSE
  <1> DEFINE Elt == CHOOSE x \in Nat : TRUE
  <1>1. Nat = {Elt} OBVIOUS
  <1>2. 0 \in Nat /\ 1 \in Nat /\ 0 # 1 OBVIOUS
  <1>3. FALSE BY <1>1, <1>2, Zenon
  <1> QED BY <1>3

====
stderr: status:failed

