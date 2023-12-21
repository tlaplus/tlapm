(* Equality of expressions up to alpha-equivalence.

When comparing expressions, this module
does not take into account any annotations
of the syntax-tree nodes.

Copyright (C) 2008-2010  INRIA and Microsoft Corporation
*)
open E_t


val expr : expr -> expr -> bool
val exprs : expr list -> expr list -> bool
val bounds : bound list -> bound list -> bool
val bound : bound -> bound -> bool
val defns : defn list -> defn list -> bool
val defn : defn -> defn -> bool
val sequent : sequent -> sequent -> bool
val hyp : hyp -> hyp -> bool
val instance : instance -> instance -> bool
