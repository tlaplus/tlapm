(*
 * reduce/nt_collect.ml --- collect data for notypes encoding
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open Util.Coll
open Property

open R_nt_table

let visitor = object (self : 'self)
  inherit [unit, nt_node Sm.t] Expr.Visit.fold as super

    (* TODO *)

  method expr scx ns oe =
    match oe.core with
    | _ -> super#expr scx ns oe
end

let collect sq =
  snd (visitor#sequent ((), Deque.empty) Sm.empty sq)
