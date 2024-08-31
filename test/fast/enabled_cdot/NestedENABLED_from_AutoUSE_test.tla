--------------------- MODULE NestedENABLED_from_AutoUSE_test -------------------
(* Test for multiply nested `ENABLED` with definitions that need expansion. *)
EXTENDS TLAPS


VARIABLE x


A == ENABLED (x /\ x')
B == ENABLED (x /\ A')
C == ENABLED (x /\ B')
D == ENABLED (x /\ C')
E == ENABLED (x /\ D')
F == ENABLED (x /\ E')
G == ENABLED (x /\ F')
H == ENABLED (x /\ G')
I == ENABLED (x /\ H')
J == ENABLED (x /\ I')


(* In this example the definitions of operators A, B, C, D, E, F, G, H, I, J
are expanded automatically because they contain primed variables in the scope
of ENABLED. For example, the operator A that occurs primed in B contains the
variable x, which is primed within the scope of ENABLED, so A is expanded
within B. In more detail, the expansions are performed because A is a state
level expression (ENABLED has this expression level) that occurs primed in
the scope of ENABLED, so it could (and does) contain variables in the scope of
a prime within the scope of ENABLED.

After AutoUSE and ExpandENABLED are applied, the resulting expression is

\E r_0 :
    \E r_0_1 :
       r_0
       /\ (\E r_0_2 :
              r_0_1
              /\ (\E r_0_3 :
                     r_0_2
                     /\ (\E r_0_4 :
                            r_0_3
                            /\ (\E r_0_5 :
                                   r_0_4
                                   /\ (\E r_0_6 :
                                          r_0_5
                                          /\ (\E r_0_7 :
                                                 r_0_6
                                                 /\ (\E r_0_8 :
                                                        r_0_7
                                                        /\ (\E r_0_9 :
                                                            r_0_8
                                                            /\ (
                                                            \E r_0_10 :
                                                            r_0_9
                                                            /\ r_0_10)))))))))

(Internally the bound constants are named with the symbol # in the identifier,
for example r#0_1, to avoid coincidence with identifiers defined by the user.)
*)
THEOREM
    ENABLED (J')
PROOF
BY ExpandENABLED, Isa, AutoUSE


================================================================================
