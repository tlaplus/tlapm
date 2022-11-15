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
        (* FIXME change 'User' to 'Builtin'? *)
        | Defn ({ core = Operator (nm, {core = Lambda ([_],_)}) }, User, _, _)
            when nm.core = with_id ->
            Some (Deque.snoc lhs h, rhs)
        | _ ->
            spin (Deque.snoc lhs h) rhs
        end
  in
  spin Deque.empty hs

let pol b = function
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
    Apply (Ix k %% [], [ Ix (n - i) %% [] ]) %% []
  end xs in
  [ withs ]

(** Effectively add a pattern "With(x)" for every bound variable "x".
    Only negative binders that require instanciation are affected.
*)
let visitor = object (self : 'self)
  inherit [bool] Expr.Visit.map as super

  method expr (b, cx as scx) oe =
    match oe.core with
    | Apply ({ core = Internal Builtin.Neg } as op, [ e ]) ->
        let e = self#expr (not b, cx) e in
        Apply (op, [ e ]) @@ oe
    | Apply ({ core = Internal Builtin.Implies } as op, [ e ; f ]) ->
        let e = self#expr (not b, cx) e in
        let f = self#expr (b, cx) f in
        Apply (op, [ e ; f ]) @@ oe
    | If (e, f, g) ->
        let e = self#expr (not b, cx) e in
        let f = self#expr (b, cx) f in
        let g = self#expr (b, cx) g in
        If (e, f, g) @@ oe
    | Case (ps, o) ->
        let ps = List.map begin fun (p, e) ->
          let p = self#expr (not b, cx) p in
          let e = self#expr (b, cx) e in
          (p, e)
        end ps in
        let o = Option.map (self#expr scx) o in
        Case (ps, o) @@ oe

    | Quant (q, bs, e) when pol b q ->
        (* Do add patterns *)
        let (b, cx as scx), bs = self#bounds scx bs in
        let xs = List.map (fun (nm, _, _) -> nm) bs in
        let k = Deque.size cx + 1 in
        let pats = mk_patterns k xs in
        let e = self#expr scx e in
        Quant (q, bs, add_pats e pats) @@ oe

    | _ -> super#expr scx oe

  method sequent scx sq =
    let (b, cx as scx), hs = self#hyps scx sq.context in
    let e = self#expr (not b, cx) sq.active in
    scx, { context = hs ; active = e }

end

let main sq =
  match search_with sq.context with
  | None -> sq
  | Some (lhs, rhs) ->
      let scx = (false, Deque.empty) in
      let _, sq = visitor#sequent scx { sq with context = rhs } in
      { sq with context = Deque.append lhs sq.context }

