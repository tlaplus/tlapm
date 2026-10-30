------------- MODULE new_bound_time_multi_test --------------

\* Expanding NEW a \in {k} inserts the declaration of a and the fact
\* a \in {k}.  The later domain {a} must be shifted by that extra fact
\* as well as by b, which is what compose (shift 1) s does.  A shift of
\* only 1 leaves a's De Bruijn index on the fact, so b \in {a} is not
\* boxed.  The theorem is valid: b \in {a} holds in every state.

EXTENDS TLAPS

CONSTANT k
VARIABLE x

THEOREM
  ASSUME NEW a \in {k},
         NEW b \in {a}
  PROVE [](b \in {a})
BY PTL

============================================================
