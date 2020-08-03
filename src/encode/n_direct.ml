(*
 * encode/direct.ml --- eliminate primitives and builtins
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Property
open Util
open Expr.T
open Type.T

module B = Builtin
module T = N_table


(* {3 Context} *)

type rty = RSet | RForm                 (** Result type *)
type aty = ASet | AOp of int * rty      (** Argument type *)
type xty = XSet | XOp of aty list * rty (** Type *)

type cx = xty Ctx.t


let to_at = function
  | RSet -> TU
  | RForm -> TBool

let to_arg = function
  | ASet -> TRg (TAtom TU)
  | AOp (n, rt) ->
      TOp (List.init n (fun _ -> TAtom TU), TAtom (to_at rt))

let to_sch = function
  | XSet -> TSch ([], [], TAtom TU)
  | XOp (ats, rt) -> TSch ([], List.map to_arg ats, TAtom (to_at rt))


let adj cx v xt =
  let v =
    match xt with
    | XSet -> assign v Props.type_prop (TAtom TU)
    | XOp _ -> assign v Props.tsch_prop (to_sch xt)
  in
  (v, Ctx.adj cx v.core xt)

let adjs cx vs xts =
  let rvs, cx =
    List.fold_left2 begin fun (rvs, cx) v xt ->
      let v, cx = adj cx v xt in
      (v :: rvs, cx)
    end ([], cx) vs xts
  in
  (List.rev rvs, cx)

let bump cx = Ctx.bump cx

let lookup_id cx n =
  Option.get (snd (Ctx.index cx n))


(* {3 Helpers} *)

let error ?at mssg =
  Errors.bug ?at mssg

let maybe_cast = function
  | RSet -> fun e -> e
  | RForm -> fun e ->
      let smb = T.std_smb (T.Ucast (TAtom TBool)) in
      let op = Opaque (T.get_name smb) %% [] in
      let op = assign op T.smb_prop smb in
      Apply (op, [ e ]) %% []

let maybe_proj = function
  | RForm -> fun e -> e
  | RSet -> fun e ->
      let smb = T.std_smb (T.Any (TAtom TU)) in
      let any = Opaque (T.get_name smb) %% [] in
      let any = assign any T.smb_prop smb in
      let op = Internal B.Eq %% [] in
      let op = assign op Props.targs_prop [ TAtom TU ] in
      Apply (op, [ e ; any ]) %% []

let aty_to_xty = function
  | ASet -> XSet
  | AOp (n, rt) -> XOp (List.init n (fun _ -> ASet), rt)


(* {3 Main} *)

let rec expr cx oe =
  let oe =
    match query oe pattern_prop with
    | None -> oe
    | Some pats ->
        let pats =
          List.map begin fun pat ->
            List.map begin fun e ->
              fst (expr cx e)
            end pat
          end pats
        in
        assign oe pattern_prop pats
  in
  match oe.core with
  | Ix n ->
      let xt = lookup_id cx n in
      begin if xt <> XSet then
        error ~at:oe "Not a set variable"
      end;
      (Ix n @@ oe, RSet)

  (* This module excludes operators that take boolean arguments from the
   * context, because that simplifies the process.  For this reason,
   * the regular connectives of propositional logic must be treated as
   * separate cases. *)
  | Internal (B.TRUE | B.FALSE) ->
      (oe, RForm)
  | Apply ({ core = Internal (B.Implies | B.Equiv | B.Conj | B.Disj) } as op, [ e ; f ]) ->
      let e, rt1 = expr cx e in
      let f, rt2 = expr cx f in
      (Apply (op, [ maybe_proj rt1 e ; maybe_proj rt2 f ]) @@ oe, RForm)
  | Apply ({ core = Internal B.Neg } as op, [ e ]) ->
      let e, rt = expr cx e in
      (Apply (op, [ maybe_proj rt e ]) @@ oe, RForm)
  | Apply ({ core = Internal (B.Eq | B.Neq) } as op, [ e ; f ]) ->
      let e, rt1 = expr cx e in
      let f, rt2 = expr cx f in
      if rt1 = rt2 then
        (Apply (op, [ e ; f ]) @@ oe, RForm)
      else
        (Apply (op, [ maybe_cast rt1 e ; maybe_cast rt2 f ]) @@ oe, RForm)

  | Apply (op, args) ->
      let op, xt = eopr cx op in
      begin match xt, args with
      | XSet, [] ->
          (Apply (op, args) @@ oe, RSet)
      | XSet, _ ->
          error ~at:oe "Application with incorrect number of arguments"
      | XOp (ats1, _), _ when List.length ats1 <> List.length args ->
          error ~at:oe "Application with incorrect number of arguments"
      | XOp (ats1, rt), _ ->
          let args_ats = List.map (earg cx) args in
          let rargs =
            List.fold_left2 begin fun rargs at1 (arg, at2) ->
              if at1 = at2 then
                arg :: rargs
              else
                error~at:arg "Bad argument shape"
            end [] ats1 args_ats
          in
          (Apply (op, List.rev rargs) @@ oe, rt)
      end

  | If (e, f, g) ->
      let e, rt1 = expr cx e in
      let f, rt2 = expr cx f in
      let g, rt3 = expr cx g in
      if rt2 = rt3 then
        (If (maybe_proj rt1 e, f, g) @@ oe, rt2)
      else
        (If (maybe_proj rt1 e, maybe_cast rt2 f, maybe_cast rt3 g) @@ oe, RSet)

  | Case (ps, None) ->
      (* Assuming the cases are incomplete, return type is set *)
      let ps =
        List.map begin fun (p, e) ->
          let p, rt1 = expr cx p in
          let e, rt2 = expr cx e in
          (maybe_proj rt1 p, maybe_cast rt2 e)
        end ps
      in
      (Case (ps, None) @@ oe, RSet)

  | Case (ps, Some o) ->
      (* Return type is form if all cases are form; otherwise set *)
      let ps_rts =
        List.map begin fun (p, e) ->
          let p, rt1 = expr cx p in
          let e, rt2 = expr cx e in
          ((maybe_proj rt1 p, e), rt2)
        end ps
      in
      let o, rt = expr cx o in
      let ps, o, rt =
        match ps_rts with
        | [] -> ([], o, RSet)
        | (p, rt1) :: ps_rts ->
            if List.for_all ((=) rt1) (rt :: List.map snd ps_rts) then
              (p :: List.map fst ps_rts, o, rt1)
            else
              let ps =
                List.map begin fun ((p, e), rt) ->
                  (p, maybe_cast rt e)
                end ((p, rt1) :: ps_rts)
              in
              (ps, maybe_cast rt o, RSet)
      in
      (Case (ps, Some o) @@ oe, rt)

  | List (b, es) ->
      let es =
        List.map begin fun e ->
          let e, rt = expr cx e in
          maybe_proj rt e
        end es
      in
      (List (b, es) @@ oe, RForm)

  | Sequent sq ->
      let sq = sequent cx sq in
      (Sequent sq @@ oe, RForm)

  | Let (dfs, e) ->
      let cx, dfs = defns cx dfs in
      let e, rt = expr cx e in
      (Let (dfs, e) @@ oe, rt)

  | Quant (q, bs, e) ->
      let cx, bs = bounds cx bs in
      let e, rt = expr cx e in
      (Quant (q, bs, maybe_proj rt e) @@ oe, RForm)

  | Tquant (q, vs, e) ->
      let cx, rvs =
        List.fold_left begin fun (cx, rvs) v ->
          let v, cx = adj cx v XSet in
          (cx, v :: rvs)
        end (cx, []) vs
      in
      let e, rt = expr cx e in
      (Tquant (q, List.rev rvs, maybe_proj rt e) @@ oe, RForm)

  | Choose (v, b, e) ->
      error ~at:oe "Not implemented"

  (* Cases below may be unnecessary, or unsound, I don't know *)

  | With (e, m) ->
      let e, rt = expr cx e in
      (With (e, m) @@ oe, rt)

  | Parens (e, pf) ->
      let e, rt = expr cx e in
      (Parens (e, pf) @@ oe, rt)

  | Bang (e, sels) ->
      let e, rt = expr cx e in
      let sels =
        List.map begin fun sel ->
          match sel with
          | Sel_inst es ->
              let es =
                List.map begin fun e ->
                  let e, rt = expr cx e in
                  maybe_cast rt e
                end es
              in
              Sel_inst es
          | Sel_lab (s, es) ->
              let es =
                List.map begin fun e ->
                  let e, rt = expr cx e in
                  maybe_cast rt e
                end es
              in
              Sel_lab (s, es)
          | _ -> sel
        end sels
      in
      (Bang (e, sels) @@ oe, rt)

  | At b ->
      (At b @@ oe, RSet)

  | _ -> error ~at:oe "Not implemented"

and eopr cx op =
  match op.core with
  | Ix n ->
      let xt = lookup_id cx n in
      (Ix n @@ op, xt)

  | Lambda (xs, e) ->
      let cx, rxs, rats =
        List.fold_left begin fun (cx, rxs, rats) (v, shp) ->
          let at =
            match shp with
            | Shape_expr -> ASet
            | Shape_op n -> AOp (n, RSet)
          in
          let v, cx = adj cx v (aty_to_xty at) in
          (cx, (v, shp) :: rxs, at :: rats)
        end (cx, [], []) xs
      in
      let e, rt = expr cx e in
      (Lambda (List.rev rxs, e) @@ op, XOp (List.rev rats, rt))

  | _ ->
      let e, rt = expr cx op in
      (maybe_cast rt e $$ op, XSet)


and earg cx oa =
  match oa.core with
  | Ix n ->
      let xt = lookup_id cx n in
      let at =
        match xt with
        | XSet -> ASet
        | XOp (ats, rt) ->
            List.iter begin function
              | AOp _ -> error ~at:oa "Second-order operator cannot be an argument"
              | _ -> ()
            end ats;
            AOp (List.length ats, rt)
      in
      (Ix n @@ oa, at)

  | Lambda (xs, e) ->
      let cx, rxs =
        List.fold_left begin fun (cx, rxs) (v, shp) ->
          begin match shp with
          | Shape_op n -> error ~at:oa "Second-order lambda-abstraction cannot be an argument"
          | _ -> ()
          end;
          let v, cx = adj cx v XSet in
          (cx, (v, shp) :: rxs)
        end (cx, []) xs
      in
      let e, rt = expr cx e in
      (Lambda (List.rev rxs, e) @@ oa, AOp (List.length xs, rt))

  | _ ->
      let e, rt = expr cx oa in
      (maybe_cast rt e $$ oa, ASet)

and bound cx (v, k, d) =
  let d =
    match d with
    | Domain d ->
        let d, rt = expr cx d in
        Domain (maybe_cast rt d)
    | _ -> d
  in
  (v, k, d)

and bounds cx bs =
  let cx, rbs =
    List.fold_left begin fun (cx, rbs) b ->
      let (v, k, d) = bound cx b in
      let v, cx = adj cx v XSet in
      (cx, (v, k, d) :: rbs)
    end (cx, []) bs
  in
  (cx, List.rev rbs)

and defn cx df =
  match df.core with
  | Operator (v, e) ->
      let e, xt = eopr cx e in
      let v, cx = adj cx v xt in
      (cx, Operator (v, e) @@ df)

  | _ -> error ~at:df "Not implemented"

and defns cx dfs =
  let cx, rdfs =
    List.fold_left begin fun (cx, rdfs) df ->
      let cx, df = defn cx df in
      (cx, df :: rdfs)
    end (cx, []) dfs
  in
  (cx, List.rev rdfs)

and hyp cx h =
  match h.core with
  | Fresh (v, shp, k, d) ->
      let d =
        match d with
        | Unbounded -> Unbounded
        | Bounded (e, vis) ->
            let e, rt = expr cx e in
            Bounded (maybe_cast rt e, vis)
      in
      let at =
        match shp with
        | Shape_expr -> ASet
        | Shape_op n -> AOp (n, RSet)
      in
      let v, cx = adj cx v (aty_to_xty at) in
      (cx, Fresh (v, shp, k, d) @@ h)

  | Flex v ->
      let v, cx = adj cx v XSet in
      (cx, Flex v @@ h)

  | Defn (df, wd, vis, ex) ->
      let cx, df = defn cx df in
      (cx, Defn (df, wd, vis, ex) @@ h)

  | Fact (e, vis, tm) ->
      let e, rt = expr cx e in
      let cx = bump cx in
      (cx, Fact (maybe_proj rt e, vis, tm) @@ h)

and hyps cx hs =
  match Deque.front hs with
  | None ->
      (cx, Deque.empty)
  | Some (h, hs) ->
      let cx, h = hyp cx h in
      let cx, hs = hyps cx hs in
      (cx, Deque.cons h hs)

and sequent cx sq =
  let cx, hs = hyps cx sq.context in
  let e, rt = expr cx sq.active in
  { context = hs ; active = maybe_proj rt e }

let main sq =
  sequent Ctx.dot sq

