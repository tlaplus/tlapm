---- MODULE everythingisafcn_test ----

EXTENDS TLAPS

(** Functions in TLA+ are guarded by a predicate IsAFcn to separate them from
    other values.  IsAFcn occurs in the axioms of TLA+ only.  If the condition
    IsAFcn is dropped, the theory of TLA+ makes the statement "Everything is a
    function" valid.
*)

THEOREM \A f : \E a, b : f \in [ a -> b ]
<1> TAKE f
<1> DEFINE a == DOMAIN f
<1> DEFINE b == { f[x] : x \in a }
<1>1 f \in [ a -> b ]
    <2>1 DOMAIN f = a
        (*OBVIOUS*)
    <2>2 \A x \in a : f[x] \in b
        (*OBVIOUS*)
    <2> QED
        BY ONLY <2>1, <2>2
<1> QED
    (*BY ONLY <1>1*)

====
stderr: status:failed
