(*
 * encode/axiomatize.ml --- add axioms in a sequent
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Property
open Expr.T

open N_table
open N_canon


(* {3 Contexts} *)

type ectx = SmbSet.t * expr Deque.dq

let init_ectx = (SmbSet.empty, Deque.empty)


(* {3 Helpers} *)

let error ?at mssg =
  Errors.bug ?at ("Encode.Axiomatize: " ^ mssg)


(* {3 Main} *)

let axioms smb = [] (* TODO *)

let add_smb smb (smbs, facts as ecx) =
  if SmbSet.mem smb smbs then
    ecx
  else
    let smbs =
      SmbSet.add smb smbs
    in
    let facts =
      List.fold_left Deque.snoc facts (axioms smb)
    in
    (smbs, facts)

let collect_visitor = object (self : 'self)
  inherit [unit, ectx] Expr.Visit.fold as super

  method expr scx ecx oe =
    match oe.core with
    | Opaque _ when has_smb oe ->
        let smb = get_smb oe in
        add_smb smb ecx

    | _ -> super#expr scx ecx oe
end

let collect sq =
  let scx = ((), Deque.empty) in
  let ecx = init_ectx in
  snd (collect_visitor#sequent scx ecx sq)

let assemble ecx sq =
  error "not implemented" (* TODO *)

