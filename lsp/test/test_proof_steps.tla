---- MODULE test_proof_steps ----

(*
This file is just to check how proof steps are identified for the
steps that take no explicit proofs, but actually generate an obligation.
I.e. HAVE, TAKE, WITNESS.
See: https://lamport.azurewebsites.net/tla/tla2-guide.pdf
*)

THEOREM
    ASSUME NEW P(_)
    PROVE (\A n : P(n)) => \E n : P(n)
    <1>1. HAVE \A n : P(n) \* Destruct the implication in the goal.
    <1>2. \A n : P(n)
        <2>1. TAKE n \* Prove forall.
        <2>2. P(n) BY <1>1
        <2>q. QED BY <2>2
    <1>3. PICK n : P(n) BY <1>1
    <1>4. WITNESS n
    <1>q. QED BY <1>1

====
