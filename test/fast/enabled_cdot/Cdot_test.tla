---------------------------- MODULE Cdot_test ----------------------------------
(* Tests for the expansion of the operator \cdot. *)
(* EXTENDS TLAPS *)

(* The proof directives below are from the module `TLAPS`.
Including them here to compare the number of definitions
with when extending the module `TLAPS`.
*)

Zenon == TRUE (*{ by (prover:"zenon") }*)

ExpandENABLED == TRUE  (*{ by (prover:"expandenabled") }*)
ExpandCdot == TRUE  (*{ by (prover:"expandcdot") }*)
AutoUSE == TRUE  (*{ by (prover:"autouse") }*)


--------------------------------------------------------------------------------
(* Unit test with a single variable. *)

VARIABLE x

R == x' = TRUE

A == /\ x = FALSE
     /\ R

B == /\ x = TRUE
     /\ x' = FALSE

C == A \cdot B

D == /\ x = FALSE
     /\ x' = FALSE


(* The definitions of the operators C and D are expanded because this is
necessary to apply the proof directive ExpandCdot and prove the assertion.
The definitions of operators A and R are expanded because together they contain
a primed variable in the first argument of \cdot, which is bound by \cdot.
The definition of operator B is expanded because it contains an unprimed
variable within the second argument of \cdot, so this unprimed variable is
bound by \cdot.

The proof directive ExpandCdot converts C with A, B, and R expanded to the
expression

\E u:  /\ /\ x = FALSE
          /\ u = TRUE
       /\ /\ u = TRUE
          /\ x' = FALSE

which is equivalent to the definition of operator D.
*)
THEOREM C <=> D
PROOF
BY ExpandCdot, Zenon DEF A, B, R, C, D


(* This theorem differs from the previous one in the presence of the proof
directive AutoUSE. The definitions of the operators A, B, and R are expanded
automatically by AutoUSE, because they contain primed and unrpimed variables in
the first and second arguments of the operator \cdot, respectively. These
expansions ensure sound reasoning about the operator \cdot.
*)
THEOREM C <=> D
PROOF
BY ExpandCdot, AutoUSE, Zenon DEF C, D


--------------------------------------------------------------------------------
(* Unit test with two variables. *)

VARIABLE y


A2 == /\ x = TRUE /\ y = FALSE
      /\ x' = FALSE /\ y' = TRUE

B2 == /\ x = FALSE /\ y = TRUE
      /\ x' = TRUE /\ y' = TRUE

C2 == A2 \cdot B2

D2 == /\ x = TRUE /\ y = FALSE
      /\ x' = TRUE /\ y' = TRUE


(* The definitions of the operators C2, D2 need to be expanded to prove the
assertion by making the operator \cdot visible to the proof directive
ExpandCdot and the definition of D2 visible to the Zenon backend.
The definitions of A2 and B2 need to be expanded because these operators occur
as first and second argument to \cdot, and contain primed and unprimed
variables, respectively. Application of the proof directive ExpandCdot produces
the expression

(\E r_0, r_1 :
             /\ /\ x = TRUE /\ y = FALSE
                /\ r_1 = FALSE /\ r_0 = TRUE
             /\ /\ r_1 = FALSE /\ r_0 = TRUE
                /\ x' = TRUE /\ y' = TRUE)
         <=> (/\ x = TRUE /\ y = FALSE
              /\ x' = TRUE /\ y' = TRUE)

(Internally the symbol # is used instead of underscores in the identifiers
r_0 and r_1, to avoid coincidence with identifiers defined by the user.)
*)
THEOREM C2 <=> D2
PROOF
BY ExpandCdot, Zenon DEF A2, B2, C2, D2


(* Similar to the previous theorem, with the difference that the proof
directive AutoUSE is included, which automatically expands the definitions of
the operators A2 and B2.
*)
THEOREM C2 <=> D2
PROOF
BY ExpandCdot, AutoUSE, Zenon DEF C2, D2


================================================================================
