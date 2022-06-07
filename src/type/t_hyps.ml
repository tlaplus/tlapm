(*
 * type/hyps.ml --- search for type hypotheses
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open Ext
open Property

open T_t

module B = Builtin


let error ?at mssg =
  let mssg = "Type.Hyps: " ^ mssg in
  failwith mssg

type 'a ret = 'a option Lazy.t

let (||>) (f : 'a ret) (g : 'a ret) : 'a ret =
  match Lazy.force f with
  | Some x -> Lazy.from_val (Some x)
  | None -> g

let (&&>) (f : 'a ret) (g : 'a ret) : 'a ret =
  match Lazy.force f with
  | None -> Lazy.from_val None
  | Some x -> begin
    match Lazy.force g with
    | Some y when x = y -> Lazy.from_val (Some y)
    | _ -> Lazy.from_val None
  end


type scx = hyp Deque.dq

let search_type_hyp ~inferer ~pol scx oe =
  let rec visit ~pol ix scx oe =
    match oe.core with
    | Apply ({ core = Internal (B.Mem | B.Notmem as b) }, [ { core = Ix n } ; e ])
      when n = ix && ((pol && b = B.Notmem) || (not pol && b = B.Mem)) ->
        begin try
          begin
          match inferer scx e with
          | TSet ty0 | TFSet ty0 -> Lazy.from_val (Some ty0)
          | _ -> Lazy.from_val None
          end
        with _ -> Lazy.from_val None
        end

    | Apply ({ core = Internal (B.Eq | B.Neq as b) }, [ { core = Ix n } ; e ])
    | Apply ({ core = Internal (B.Eq | B.Neq as b) }, [ e ; { core = Ix n } ])
      when n = ix && ((pol && b = B.Neq) || (not pol && b = B.Eq)) ->
        begin try
          Lazy.from_val (Some (inferer scx e))
        with _ -> Lazy.from_val None
        end

    | Apply ({ core = Internal B.IsFiniteSet }, [ { core = Ix n } ])
      when n = ix && not pol ->
        Lazy.from_val (Some (TFSet (TAtm TAIdv)))

    | Apply ({ core = Internal (B.Disj | B.Conj as b) }, [ e ; f ])
      when (pol && b = B.Disj) || (not pol && b = B.Conj) ->
        visit ~pol ix scx e ||>
        visit ~pol ix scx f

    | Apply ({ core = Internal (B.Disj | B.Conj as b) }, [ e ; f ])
      when (not pol && b = B.Disj) || (pol && b = B.Conj) ->
        visit ~pol ix scx e &&>
        visit ~pol ix scx f

    | List ((Or | And as b), es)
      when (pol && b = Or) || (not pol && b = And) ->
        List.fold_left begin fun r e ->
          r ||> visit ~pol ix scx e
        end (Lazy.from_val None) es

    | List ((Or | And as b), es)
      when (not pol && b = Or) || (pol && b = And) ->
        List.fold_left begin fun r e ->
          r &&> visit ~pol ix scx e
        end (Lazy.from_val None) es

    | Apply ({ core = Internal B.Neg }, [ e ]) ->
        visit ~pol:(not pol) ix scx e

    | Apply ({ core = Internal B.Implies }, [ e ; f ]) ->
        visit ~pol:(not pol) ix scx e ||>
        visit ~pol ix scx f

    | Quant (q, bs, e)
      when (pol && q = Forall) || (not pol && q = Exists) ->
        let n = List.length bs in
        let scx =
          List.fold_left begin fun scx (v, _, _) ->
            (* This is *probably* unsafe, so I'm disabling it for now *)
            (*let v = assign v Props.ty0_prop (TAtm TAIdv) in*)
            let h = Fresh (v, Shape_expr, Constant, Unbounded) %% [] in
            Deque.snoc scx h
          end scx bs
        in
        visit ~pol (ix + n) scx e

    | Sequent sq when pol ->
        visit_sq ix scx sq

    | _ -> Lazy.from_val None

  and visit_sq ix scx sq =
    let rec spin ix scx hs =
      match Deque.front hs with
      | Some ({ core = Fact (e, Visible, _) } as h, hs) ->
          visit ~pol:false ix scx e ||>
          spin (ix + 1) (Deque.snoc scx h) hs
      | Some (h, hs) ->
          spin (ix + 1) (Deque.snoc scx h) hs
      | None ->
          Lazy.from_val None
    in
    spin ix scx sq.context ||>
    visit ~pol:true (ix + Deque.size sq.context) scx sq.active
  in

  let dummy = Fact (Internal B.TRUE %% [], Visible, NotSet) %% [] in
  let scx = Deque.snoc scx dummy in
  Lazy.force (visit ~pol 1 scx oe)

