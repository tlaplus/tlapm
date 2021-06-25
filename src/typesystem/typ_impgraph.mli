(************************************************************************
*  typ_impgraph.mli
*
*
*  Created by Hernán Vanzetto on 4 Nov 2013.
Copyright (c) 2013  INRIA and Microsoft Corporation
************************************************************************)

open Expr.T
open Typ_t
open Typ_e

val solve:
  (hyp list * expr) SMap.t ->
  (Builtin.builtin * Typ_e.t * tref * tref) list ->
  string list ->
  (hyp list * expr) SMap.t
