------------- MODULE issue235_set_enum_two_elements_stest --------------

\* https://github.com/tlaplus/tlapm/issues/235
\* {e \in S, a \in S} is the enumeration of two Booleans, so it is not
\* empty.  The tlapm parser reads both elements as bounds and drops them.
\* The theorem is false.

CONSTANTS a, e, S

THEOREM {e \in S, a \in S} = {}
OBVIOUS

=====================================================================
