------------- MODULE fresh_op_modality_test --------------

EXTENDS TLAPS

CONSTANT P(_)
VARIABLE x

THEOREM <>(P(x)) => <>(P(x))
BY SMT, Isa

THEOREM ENABLED (P(x)) => ENABLED (P(x))
BY SMT, Isa

THEOREM ((P(x)) \cdot (x' = x)) => ((P(x)) \cdot (x' = x))
BY SMT, Isa

LEMMA EnabledR ==
  ASSUME NEW R(_, _)
  PROVE ENABLED R(x, x) <=> R(x, x)
BY ExpandENABLED

THEOREM ASSUME NEW R(_, _), R(x, x) PROVE ENABLED R(x, x)
BY Isa, EnabledR

==========================================================
\* SMT proves the modal steps. Isabelle proves the last theorem.
\* A backend error must not abort the module.
stderr: prover:smt
stderr: prover:smt
stderr: prover:smt
stderr: prover:isabelle
stderr: All 14 obligations proved.
nostderr: status:failed
nostderr: Unexpected error in SMT back-end
nostderr: Unexpected exception
nostd*: ending abnormally
