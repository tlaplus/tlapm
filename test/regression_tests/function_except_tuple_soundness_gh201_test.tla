---- MODULE function_except_tuple_soundness_gh201 ----
EXTENDS TLAPS, Naturals

THEOREM SoundnessError == FALSE
  <1> DEFINE f1 == [i \in Nat |-> i]
  <1> DEFINE f2 == [f1 EXCEPT ![0] = << 0 >>]
  <1>1. f1 = f2 OBVIOUS
  <1> QED BY <1>1

====
stderr: status:failed

