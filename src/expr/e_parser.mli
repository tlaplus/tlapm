(* Parser of expressions.

Copyright (C) 2008-2010  INRIA and Microsoft Corporation
*)
open Tla_parser
open E_t


val expr : bool -> expr lprs
val bounds : bool -> bound list lprs
val defn : bool -> defn lprs
val instance : bool -> instance lprs
val subst : bool -> (Util.hint * expr) list lprs
val hyp : bool -> hyp lprs
val sequent : bool -> sequent lprs
val opdecl : (Util.hint * shape) lprs
