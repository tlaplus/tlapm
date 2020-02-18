(*
 * reduce/nt_collect.mli --- collect data for notypes encoding
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open Util.Coll

val collect : sequent -> R_nt_table.nt_node Sm.t
