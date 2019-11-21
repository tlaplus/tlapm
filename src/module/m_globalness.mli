(*
 * module/globalness.ml --- detect global operators
 *
 *
 * Copyright (C) 2008-2013  INRIA and Microsoft Corporation
 *)

open M_t;;


val is_global : 'a Property.wrapped -> bool

val globalness : mule -> mule
