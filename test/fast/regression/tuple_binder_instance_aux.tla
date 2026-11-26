---------- MODULE tuple_binder_instance_aux -----------
CONSTANT S
Sym == \A <<a, b>> \in S \X S : (a = b) => (b = a)
Diag == {<<u, v>> \in S \X S : u = v}
====================================
