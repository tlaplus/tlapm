----------- MODULE tuple_binder_instance_test -----------------
(* Tuple binders in an instantiated module must be desugared when loading it. *)
I == INSTANCE tuple_binder_instance_aux WITH S <- BOOLEAN

THEOREM I!Sym
BY DEF I!Sym

THEOREM <<TRUE, TRUE>> \in I!Diag
BY DEF I!Diag
==========================================
