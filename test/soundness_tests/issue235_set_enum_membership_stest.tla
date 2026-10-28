------------- MODULE issue235_set_enum_membership_stest --------------

\* https://github.com/tlaplus/tlapm/issues/235
\* {e \in S} is the enumeration of the single Boolean e \in S, so it is
\* not empty.  The tlapm parser drops elements of the form e \in S from
\* set enumerations and reads it as {}.  The theorem is false.

CONSTANTS e, S

THEOREM {e \in S} = {}
OBVIOUS

=====================================================================
known: https://github.com/tlaplus/tlapm/issues/235
