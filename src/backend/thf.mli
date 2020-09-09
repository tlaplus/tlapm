(*
 * backend/thf.ml --- translation to TPTP/THF
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** Print in THF format a sequent (possibly higher-order)
    without TLA+ primitives
*)
val pp_print_obligation : ?solver:string -> Format.formatter -> Proof.T.obligation -> unit;;

