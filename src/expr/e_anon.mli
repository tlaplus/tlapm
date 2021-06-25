(*
 * expr/anon.mli --- expressions (anonymization)
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open E_t

val hyp_is_named: string -> hyp -> bool

class anon: [string list] E_visit.map

val anon: anon
