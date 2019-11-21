(************************************************************************
*  smt3.mli
*  
*
*  Created by Hernán Vanzetto on 9 Dec 2013.
*  Copyright (c) 2013 __MyCompanyName__. All rights reserved.
************************************************************************)

val encode_smtlib : ?solver:string -> Format.formatter -> Proof.T.obligation -> unit
val encode_fof : Format.formatter -> Proof.T.obligation -> unit

type smt_logic =
  | AUFNIRA
  | UFNIA

val to_string : smt_logic -> string

val pp_print_obligation : ?solver:string -> ?logic:smt_logic -> Format.formatter -> Proof.T.obligation -> unit

