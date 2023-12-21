(***************************************************************************
 This is a proof-exercise. The aim is to apply what we have learned in
 Basics.tla, and to prove the theorem Correctness.

 The theorem states that Euclid's algorithm (as specified by Spec) does
 indeed produce the greatest common denominator of two numbers M and N.
 (Compare [Hyperbook, Section 4].)

 At the end of the file you will find some hints that may be useful when
 you're stuck.
 ***************************************************************************)


-------------------- MODULE exercise_Euclid --------------------
EXTENDS Integers, TLAPS


(*******************************************
    SOME AUXILIARY DEFINITIONS
 *******************************************)

(* p | q : p divides q *)
p | q == \E d \in 1..q : q = p * d

(* Divisors(q) : set of all integers less than or equal than q that divide q. *)
Divisors(q) == {d \in 1..q : d | q}

(* Maximum(S) : greatest element of S *)
Maximum(S) == CHOOSE x \in S : \A y \in S : x \geq y

(* Greatest Common Denominator *)
GCD(p,q) == Maximum(Divisors(p) \cap Divisors(q))



(*******************************************
    INPUT
 *******************************************)
CONSTANTS M, N

ASSUME NumberAssumption == M \in (Nat \ {0})
                        /\ N \in (Nat \ {0})


(*******************************************
    SPECIFICATION OF EUCLID'S ALGORITHM
 *******************************************)
VARIABLES x, y

Init == (x = M) /\ (y = N)

Next == (x < y /\ y' = y - x /\ x' = x)
     \/ (y < x /\ x' = x-y   /\ y' = y)



Spec == Init /\ [][Next]_<<x,y>>



ResultCorrect == (x = y) => x = GCD(M, N)

THEOREM Correctness == Spec => []ResultCorrect

=======================================================

(***************************************************************************
*Hint:*
    The following three things are true about GCD:

    GCD_refl        == \A p    \in Number : GCD(p, p) = p
    GCD_commutative == \A p, q \in Number : GCD(p, q) = GCD(q, p)
    GCD_lt          == \A p, q \in Number : (p < q) => GCD(p, q) = GCD(p, q-p)

    You may one to prove that they do, and then use them in your proof.
 ***************************************************************************)


(***************************************************************************
*Hint:*
    ResultCorrect is not a good invariant, since it is not informative until
    x = y. We will need an invariant that entails ResultCorrect, and that
    is always true and informative.

    Try coming up with a more useful one yourself, or use the following:

    Inv == x \in Number
        /\ y \in Number
        /\ GCD(x, y) = GCD(M, N)

 ***************************************************************************)
