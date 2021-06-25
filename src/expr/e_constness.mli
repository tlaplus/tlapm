(*
 * expr/constness.ml --- detect constant operators
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open E_t
open E_visit


(* returns the const value of the term *)
val is_const : 'a Property.wrapped -> bool
(* checks if const was already computed for this term *)
val has_const : 'a Property.wrapped -> bool

class virtual const_visitor : [unit] E_visit.map
