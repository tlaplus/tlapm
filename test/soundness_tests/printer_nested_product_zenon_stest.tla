------------- MODULE printer_nested_product_zenon_stest --------------
EXTENDS TLAPS
VARIABLE x

\* Correct:   [](x \in ({1} \X ({2} \X {3})))
\* Incorrect: [](x \in ({1} \X {2} \X {3}))
\* Counterexample: x is always <<1, <<2, 3>>>>.
\* The old printer merged the two boxed predicates during coalescing.

THEOREM
  [](x \in ({1} \X ({2} \X {3})))
  => [](x \in ({1} \X {2} \X {3}))
BY Zenon

=====================================================================
