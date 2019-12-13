(*
 * backend/smtlib.ml --- direct translation to SMT-LIB
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev$";;

(* TODO: do this *)
let pp_print_obligation ?(solver="CVC4") ppf obl =
  Errors.bug "Backend.Smtlib.pp_print_obligation"
