----------- MODULE tuple_binder_extends_test -----------------
(* Tuple binders in an extended module must be desugared when loading it. *)
EXTENDS tuple_binder_extends_aux

THEOREM Sym(BOOLEAN)
BY DEF Sym
==========================================
