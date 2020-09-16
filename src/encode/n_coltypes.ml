(*
 * encode/coltypes.ml --- collect types in an expression
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Property

open Expr.T
open Type.T


(* {3 Helpers} *)

let add_ty ss ty =
  Ts.add ty ss

let add_from_ty1 ss = function
  | Ty1 (ty0s, ty) ->
      List.fold_left add_ty ss (ty :: ty0s)

let add_from_ty2 ss = function
  | Ty2 (ty1s, ty) ->
      List.fold_left add_from_ty1 (add_ty ss ty) ty1s


(* Add to [ss] all types from annotations of [h]
 * If no annotations then [ss] is unchanged *)
let gather_types ss h =
  let ss = Option.fold add_ty ss (query h Props.ty0_prop) in
  let ss = Option.fold add_from_ty1 ss (query h Props.ty1_prop) in
  let ss = Option.fold add_from_ty2 ss (query h Props.ty2_prop) in
  ss


(* {3 Main} *)

let visitor = object (self : 'self)
  inherit [unit, Ts.t] Expr.Visit.fold as super

  method expr scx ss oe =
    match oe.core with
    | Lambda (xs, _) ->
        let ss =
          List.fold_left begin fun ss (h, _) ->
            (* NOTE lambdas as expressions are first-order, so
             * all annotations are expected to be types *)
            gather_types ss h
          end ss xs
        in
        super#expr scx ss oe
    | Tquant (_, xs, _) ->
        let ss = List.fold_left gather_types ss xs in
        super#expr scx ss oe
    | Choose (x, _, _) ->
        let ss = gather_types ss x in
        super#expr scx ss oe
    | SetSt (x, _, _) ->
        let ss = gather_types ss x in
        super#expr scx ss oe
    | _ -> super#expr scx ss oe

  method bounds scx ss bs =
    let ss =
      List.fold_left begin fun ss (h, _, _) ->
        gather_types ss h
      end ss bs
    in
    super#bounds scx ss bs

  method defn scx ss df =
    match df.core with
    | Operator (h, { core = Lambda _ }) ->
        let ss = gather_types ss h in
        super#defn scx ss df
    | Operator (h, _) ->
        let ss = gather_types ss h in
        super#defn scx ss df
    | _ -> super#defn scx ss df

  method hyp scx ss h =
    match h.core with
    (* NOTE Shape_op 0 is used for declarations inserted by Encode.Axiomatize *)
    | Fresh (v, Shape_op n, _, _) ->
        let ss = gather_types ss v in
        super#hyp scx ss h
    | Fresh (v, Shape_expr, _, _) ->
        let ss = gather_types ss v in
        super#hyp scx ss h
    | Flex v ->
        let ss = gather_types ss v in
        super#hyp scx ss h
    | _ -> super#hyp scx ss h

end

let main sq =
  let scx = (), Deque.empty in
  snd (visitor#sequent scx Ts.empty sq)

