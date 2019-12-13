(*
 * backend/smtlib.ml --- direct translation to SMT-LIB
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

val pp_print_obligation : ?solver:string -> Format.formatter -> Proof.T.obligation -> unit;;
