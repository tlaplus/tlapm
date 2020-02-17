---- MODULE emdegeneracy_test ----

EXTENDS TLAPS

(** The liberal interpretation of TLA+ can be obtained by stating that every
    expression may be treated as a boolean where necessary.  But the stronger
    assertion that every expression holds a truth value (is boolean) is
    inconsistent, as shown below.
*)

EM == \A x : x = TRUE \/ x = FALSE

THEOREM ~ EM
<1> SUFFICES ASSUME EM PROVE FALSE  OBVIOUS
<1>1 \A x : x \subseteq BOOLEAN     BY DEF EM
<1>2 { "foo", "bar", "baz" } \subseteq BOOLEAN
                                    BY <1>1
<1> QED                             BY <1>2

(** Another argument: if EM holds, then BOOLEAN is the set of all sets; but
    such a set cannot exists.
*)

====
