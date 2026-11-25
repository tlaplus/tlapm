------------- MODULE printer_nested_product_ptl_stest --------------
EXTENDS TLAPS

\* Correct:   <<1, <<2, 3>>>> \in ({1} \X ({2} \X {3}))
\* Incorrect: <<1, <<2, 3>>>> \in ({1} \X {2} \X {3})
\* The old printer flattened both, giving PTL the same atom for each.

THEOREM
  ASSUME <<1, <<2, 3>>>> \in {1} \X ({2} \X {3})
  PROVE  <<1, <<2, 3>>>> \in {1} \X {2} \X {3}
BY PTL

===================================================================
