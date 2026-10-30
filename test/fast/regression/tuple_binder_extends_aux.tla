---------- MODULE tuple_binder_extends_aux -----------
Sym(S) == \A <<a, b>> \in S \X S : (a = b) => (b = a)
====================================
