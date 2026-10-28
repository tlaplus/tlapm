------------- MODULE issue235_set_enum_tuple_stest --------------

\* https://github.com/tlaplus/tlapm/issues/235
\* {<<a, e>> \in S} is the enumeration of the single Boolean <<a, e>> \in S,
\* so it is not empty.  The tlapm parser reads <<a, e>> \in S as a bound
\* and drops it.  The theorem is false.

CONSTANTS a, e, S

THEOREM {<<a, e>> \in S} = {}
OBVIOUS

=====================================================================
known: https://github.com/tlaplus/tlapm/issues/235
