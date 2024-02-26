(*
 * expr/collect.ml --- collect data from expressions
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open E_t
open E_visit
open Property

open Util.Coll

type ctx = hyp Deque.dq


(* {3 Variables} *)

type var_set = Is.t

(* Methods of this class return two sets, holding respectively unbound and
 * bound variables of the expression.  The boundary is defined by the length of
 * the context, so the methods are intended to be called with an empty context,
 * in order to get the variables free relative to some local context. *)
let collect_vars = object (self : 'self)
  inherit [unit, var_set] fold as super

  method expr (unit, hx as scx) s oe =
    match oe.core with
    | Ix n ->
        let depth = Deque.size hx in
        if n > depth then
          Is.add (n - depth) s
        else
          s
    | _ -> super#expr scx s oe

end

let vs_fold hx f is a =
  Is.fold begin fun ix a ->
    let hyp = get_val_from_id hx ix in
    f ix hyp a
  end is a

let vs_partition hx f is =
  Is.partition begin fun ix ->
    let hyp = get_val_from_id hx ix in
    f ix hyp
  end is

let get_hints hx is =
  vs_fold hx begin fun ix hyp hs ->
    let h = hyp_hint hyp in
    Hs.add h hs
  end is Hs.empty

let get_strings hx is =
  vs_fold hx begin fun ix hyp hs ->
    let h = hyp_name hyp in
    Ss.add h hs
  end is Ss.empty

let fvs ?ctx:(ctx=Deque.empty) e =
  collect_vars#expr ((), ctx) Is.empty e


(* {3 Opaques} *)

let collect_opaques = object (self : 'self)
  inherit [unit, Hs.t] fold as super

  method expr (unit, hx as scx) os oe =
    match oe.core with
    | Opaque s ->
        let h = s @@ oe in
        Hs.add h os
    | _ -> super#expr scx os oe

end

let opaques ?ctx:(ctx=Deque.empty) e =
  collect_opaques#expr ((), ctx) Hs.empty e
