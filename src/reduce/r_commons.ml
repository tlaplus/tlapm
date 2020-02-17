(*
 * reduce/commons.ml --- reduce utilities
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open Type.T
open Property


let replace s = object (self : 'self)
  inherit [unit] Expr.Visit.map as super

  method expr ((), hx as scx) oe =
    match oe.core with
    | Opaque s' when s = s' ->
        let n = Deque.size hx in
        Ix n @@ oe
    | _ -> super#expr scx oe
end

let add_hyp hyp ?opq sq =
  match opq with
  | None ->
      { sq with context = Deque.cons hyp sq.context }
  | Some s ->
      let repl = replace s in
      let _, sq = repl#sequent ((), Deque.empty) sq in
      { sq with context = Deque.cons hyp sq.context }

