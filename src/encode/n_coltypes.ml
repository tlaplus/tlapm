(*
 * encode/coltypes.ml --- collect types in an expression
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Property

open Expr.T
open Type.T

let add_ty ss ty =
  Ts.add ty ss

let more_type ss h =
  match query h Props.type_prop with
  | Some ty ->
      add_ty ss ty
  | None ->
      ss (* NOTE ignore absent annotations *)

let add_from_targ ss = function
  | TRg ty ->
      add_ty ss ty
  | TOp (tys, ty) ->
      List.fold_left add_ty ss (ty :: tys)

let more_targ ss h =
  match query h Props.targ_prop with
  | Some targ ->
      add_from_targ ss targ
  | None ->
      ss

let add_from_tsch ss = function
  | TSch ([], targs, ty) ->
      List.fold_left add_from_targ (add_ty ss ty) targs
  | TSch (_ :: _, _, _) ->
      ss (* NOTE ignore polymorphic schemes *)

let more_tsch ss h =
  match query h Props.tsch_prop with
  | Some tsch ->
      add_from_tsch ss tsch
  | None ->
      ss

let visitor = object (self : 'self)
  inherit [unit, Ts.t] Expr.Visit.fold as super

  method expr scx ss oe =
    match oe.core with
    | Lambda (xs, _) ->
        let ss =
          List.fold_left begin fun ss (h, _) ->
            (* NOTE lambdas as expressions are first-order, so
             * all annotations are expected to be types *)
            more_type ss h
          end ss xs
        in
        super#expr scx ss oe
    | Tquant (_, xs, _) ->
        let ss = List.fold_left more_type ss xs in
        super#expr scx ss oe
    | Choose (x, _, _) ->
        let ss = more_type ss x in
        super#expr scx ss oe
    | SetSt (x, _, _) ->
        let ss = more_type ss x in
        super#expr scx ss oe
    | _ -> super#expr scx ss oe

  method bounds scx ss bs =
    let ss =
      List.fold_left begin fun ss (h, _, _) ->
        more_type ss h
      end ss bs
    in
    super#bounds scx ss bs

  method defn scx ss df =
    match df.core with
    | Operator (h, { core = Lambda _ }) ->
        let ss = more_tsch ss h in
        super#defn scx ss df
    | Operator (h, _) ->
        let ss = more_type ss h in
        super#defn scx ss df
    | _ -> super#defn scx ss df

  method hyp scx ss h =
    match h.core with
    | Fresh (v, Shape_op n, _, _) when n <> 0 ->
        let ss = more_tsch ss v in
        super#hyp scx ss h
    | Fresh (v, Shape_expr, _, _) ->
        let ss = more_type ss v in
        super#hyp scx ss h
    | Flex v ->
        let ss = more_type ss v in
        super#hyp scx ss h
    | _ -> super#hyp scx ss h

end

let main sq =
  let scx = (), Deque.empty in
  snd (visitor#sequent scx Ts.empty sq)

