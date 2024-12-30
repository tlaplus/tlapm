---- MODULE quant_level_test ----
(*
The levels of quantifier bounds were ignored.
That lead to considering formulas as being constant level
leading to proofs passing were they must fail.
*)
VARIABLE v
I == \A y \in v: y = y
LEMMA ASSUME I PROVE I' OBVIOUS
====
stderr: status:failed
