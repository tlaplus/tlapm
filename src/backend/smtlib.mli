(*
 * backend/smtlib.ml --- direct translation to SMT-LIB
 *
 *
 * Copyright (C) 2022  INRIA and Microsoft Corporation
 *)

(** Print in SMT-LIB format a sequent reduced to first-order logic
    without TLA+ primitives
*)
val pp_print_obligation : ?solver:string -> Format.formatter -> Proof.T.obligation -> unit;;

