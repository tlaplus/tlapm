(*
 * reduce/nt_cook.ml
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open Type.T
open Property

module A = R_nt_axioms
module B = Builtin

let tla_prefix = "TLA__"

let setst_nm s = tla_prefix ^ "setst_" ^ s

let setst_prop = make "Reduce.Cook.setst_prop"


let visitor = object (self : 'self)
  inherit [unit] Expr.Visit.map as super

  method expr scx oe =
    match oe.core with
    (* TODO reduce to 1st order *)
    | _ -> super#expr scx oe
end

let cook sq =
  snd (visitor#sequent ((), Deque.empty) sq)
