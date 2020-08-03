(*
 * encode/hints.ml --- add generic with-patterns on quantified forms
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Property
open Expr.T

let with_id = "With"

(** Spli [hs] into [lhs] and [rhs] where [lhs] ends with
    the declaration of a "With(X)" predicate
*)
let search_with hs =
  let rec spin lhs rhs =
    match Deque.front rhs with
    | None -> None
    | Some (h, rhs) ->
        begin match h.core with
        | Fresh (nm, Shape_op 1, _, Unbounded) when nm.core = with_id ->
            Some (Deque.snoc lhs h, rhs)
        | _ ->
            spin (Deque.snoc lhs h) rhs
        end
  in
  spin Deque.empty hs

let negative_binder b = function
  | Forall -> not b
  | Exists -> b

(** Make the single sequent pattern "With(x1), .., With(xn)".
    It is assumed xs are the last variables in the context,
    so xi is just the index (n - i + 1)
*)
let mk_patterns k xs =
  let n = List.length xs in
  let withs = List.mapi begin fun i v ->
    (* NOTE use type info on v? *)
    Apply (Ix k %% [], [ Ix (n - i + 1) %% [] ]) %% []
  end xs in
  [ withs ]

(** Effectively add a pattern "With(x)" for every bound variable "x".
    Only negative binders that require instanciation are affected.
*)
let visitor = object (self : 'self)
  inherit [int * bool] Expr.Visit.map as super

  method expr ((k, b), cx as scx) oe =
    match oe.core with
    | Apply ({ core = Internal Builtin.Neg } as op, [ e ]) ->
        let e = self#expr ((k, not b), cx) e in
        Apply (op, [ e ]) @@ oe
    | Apply ({ core = Internal Builtin.Implies } as op, [ e ; f ]) ->
        let e = self#expr ((k, not b), cx) e in
        let f = self#expr ((k, b), cx) f in
        Apply (op, [ e ; f ]) @@ oe
    | If (e, f, g) ->
        let e = self#expr ((k, not b), cx) e in
        let f = self#expr ((k, b), cx) f in
        let g = self#expr ((k, b), cx) g in
        If (e, f, g) @@ oe
    | Case (ps, o) ->
        let ps = List.map begin fun (p, e) ->
          let p = self#expr ((k, not b), cx) p in
          let e = self#expr ((k, b), cx) e in
          (p, e)
        end ps in
        let o = Option.map (self#expr scx) o in
        Case (ps, o) @@ oe

    | Quant (q, bs, e) when negative_binder b q ->
        (* Do add patterns *)
        let ((k, b), cx as scx), bs = self#bounds scx bs in
        let xs = List.map (fun (nm, _, _) -> nm) bs in
        let pats = mk_patterns k xs in
        let e = self#expr scx e in
        Quant (q, bs, add_patterns e pats) @@ oe

    | Lambda (xs, _) ->
        super#expr ((k + List.length xs, b), cx) oe
    | Tquant (_, xs, _) ->
        super#expr ((k + List.length xs, b), cx) oe

    | Choose (x, d, e) ->
        let d = Option.map (self#expr scx) d in
        let e = self#expr ((k + 1, b), cx) e in
        Choose (x, d, e) @@ oe
    | SetSt (x, d, e) ->
        let d = self#expr scx d in
        let e = self#expr ((k + 1, b), cx) e in
        SetSt (x, d, e) @@ oe

    | _ -> super#expr scx oe

  method bounds scx bs =
    let ((k, b), cx), bs = super#bounds scx bs in
    ((k + List.length bs, b), cx), bs

  method sequent scx sq =
    let ((k, b), cx as scx), hs = self#hyps scx sq.context in
    let e = self#expr ((k, not b), cx) sq.active in
    scx, { context = hs ; active = e }

end

let main sq =
  match search_with sq.context with
  | None -> sq
  | Some (lhs, rhs) ->
      let init = (1, true) in
      let scx = Deque.fold_left Expr.Visit.adj (init, Deque.empty) lhs in
      let _, sq = visitor#sequent scx { sq with context = rhs } in
      { sq with context = Deque.append lhs sq.context }

