(*
 * proof/anon.mli --- anonymise proofs
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** Anonymize proofs *)

class anon : [string list] P_visit.map
val anon : anon
