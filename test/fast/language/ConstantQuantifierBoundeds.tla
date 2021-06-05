---------------------- MODULE ConstantQuantifierBoundeds -----------------------
(* Test that \E and \A allow bounded declarations. *)
E == \E x \in TRUE, y, z \in TRUE, w \in TRUE:  TRUE
A == \A x \in TRUE, y, z \in TRUE, w \in TRUE:  TRUE

Etuples == \E x \in TRUE, <<y, z>> \in TRUE \X TRUE, w \in TRUE:  TRUE
Atuples == \A x \in TRUE, <<y, z>> \in TRUE \X TRUE, w \in TRUE:  TRUE
================================================================================
