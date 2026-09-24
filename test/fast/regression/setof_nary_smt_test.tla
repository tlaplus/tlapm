---- MODULE setof_nary_smt_test ----

EXTENDS TLAPS, Naturals

THEOREM SetOfTwoBoundVariablesUsesBinaryPredicate ==
  {x + y : x \in 1..1, y \in 1..1} = {2}
BY SMT

====
