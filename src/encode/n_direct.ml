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


let error ?at mssg =
  let mssg = "Encode.Direct: " ^ mssg in
  Errors.bug ?at mssg

type rty = RSet | RForm                 (** Result type *)
type aty = ASet | AOp of int * rty      (** Argument type *)
type xty = XSet | XOp of aty list * rty (** Type *)


(* {3 Conversions} *)

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

let from_at = function
  | TU -> RSet
  | TInt -> RSet
  | TBool -> RForm
  | _ -> error "from_at: bad conversion"

let from_arg = function
  | TRg (TAtom TU) -> ASet
  | TOp (tys, TAtom at) ->
      List.iter begin function
        | TAtom TU -> ()
        | _ -> error "from_arg: bad conversion"
      end tys;
      AOp (List.length tys, from_at at)
  | _ -> error "from_arg: bad conversion"

let from_sch = function
  | TSch ([], [], TAtom TU) ->
      XSet
  | TSch ([], targs, TAtom at) ->
      XOp (List.map from_arg targs, from_at at)
  | _ -> error "from_sch: bad conversion"


(* {3 Context} *)

type cx = xty Ctx.t

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

let opq_from_smb tla_smb =
  let smb = T.std_smb tla_smb in
  let op = Opaque (T.get_name smb) %% [] in
  let op = assign op T.smb_prop smb in
  op

let maybe_cast = function
  | RSet -> fun e -> e
  | RForm -> fun e ->
      let op = opq_from_smb (T.Ucast (TAtom TBool)) in
      Apply (op, [ e ]) %% []

let maybe_proj = function
  | RForm -> fun e -> e
  | RSet -> fun e ->
      let any = opq_from_smb (T.Any (TAtom TU)) in
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
      let rt =
        match xt with
        | XSet -> RSet
        | XOp ([], rt) -> rt
        | _ -> error ~at:oe "Expected a constant type for variable"
      in
      (Ix n @@ oe, rt)

  (* NOTE It seems the only use for this case is to let primed variables pass
   * through.  x' is encoded as (Opaque "x#prime") at this point. *)
  | Opaque s ->
      (Opaque s @@ oe, RSet)

  (* Propositional connectives treated separately, because the weak type system
   * specific to this module excludes operators that take boolean arguments, or
   * boolean constants. *)
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

  (* FIXME HACK! *)
  (* Make Encode.Direct ignore already processed expressions *)
  | Apply (op, _) when has op T.smb_prop ->
      let smb = get op T.smb_prop in
      let rt =
        match T.get_sch smb with
        | TSch (_, _, TAtom at) -> from_at at
        | _ -> failwith "Bad result type"
      in
      (oe, rt)

  | Internal _ ->
      expr cx (Apply (oe, []) %% [])
  | Apply (op, args) ->
      let op, xt = eopr cx op in
      begin match xt, args with
      | XSet, [] ->
          (op $$ oe, RSet)
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

  | Choose (v, None, e) ->
      let v, cx = adj cx v XSet in
      let e, rt = expr cx e in
      let op = opq_from_smb (T.Uver (T.Choose TUnknown)) in
      (Apply (op, [ Lambda ([ v, Shape_expr ], maybe_proj rt e) %% [] ]) @@ oe, RSet)

  | Choose (v, Some b, e) ->
      let b, rt1 = expr cx b in
      let v, cx = adj cx v XSet in
      let e, rt2 = expr cx e in
      let op = opq_from_smb (T.Uver (T.Choose TUnknown)) in
      let mem = opq_from_smb (T.Uver (T.Mem TUnknown)) in
      let b = Expr.Subst.app_expr (Expr.Subst.shift 1) (maybe_cast rt1 b) in
      let e =
        Apply (Internal B.Conj %% [], [
          Apply (mem, [ Ix 1 %% [] ; b ]) %% [] ;
          maybe_proj rt2 e
        ]) %% []
      in
      (Apply (op, [ Lambda ([ v, Shape_expr ], e) %% [] ]) @@ oe, RSet)

  | SetSt (v, b, e) ->
      let b, rt1 = expr cx b in
      let v, cx = adj cx v XSet in
      let e, rt2 = expr cx e in
      let op = opq_from_smb (T.Uver (T.SetSt TUnknown)) in
      (Apply (op, [ maybe_cast rt1 b ; Lambda ([ v, Shape_expr ], maybe_proj rt2 e) %% [] ]) @@ oe, RSet)

  | SetOf (e, bs) ->
      let cx, rvs, rbs, _ =
        List.fold_left begin fun (ncx, rvs, rbs, dit) (v, _, d) ->
          match d with
          | Domain b ->
              let b, rt = expr cx b in
              let v, ncx = adj ncx v XSet in
              let b = maybe_cast rt b in
              (ncx, (v, Shape_expr) :: rvs, b :: rbs, Some b)
          | Ditto ->
              let v, ncx = adj ncx v XSet in
              let b = Option.get dit in
              (ncx, (v, Shape_expr) :: rvs, b :: rbs, dit)
          | No_domain ->
              error ~at:v "Domain expected"
        end (cx, [], [], None) bs
      in
      let e, rt = expr cx e in
      let op = opq_from_smb (T.Uver (T.SetOf (List.init (List.length bs) (fun _ -> TUnknown), TUnknown))) in
      (Apply (op, (Lambda (List.rev rvs, maybe_cast rt e) %% []) :: List.rev rbs) @@ oe, RSet)

  | SetEnum es ->
      let es =
        List.map begin fun e ->
          let e, rt = expr cx e in
          maybe_cast rt e
        end es
      in
      let n = List.length es in
      let op = opq_from_smb (T.Uver (T.SetEnum (n, TUnknown))) in
      (Apply (op, es) @@ oe, RSet)

  (* Ignoring Product, Tuple, and Fcn with more than one arg.
   * These should be encoded away *)

  | Fcn ([ v, _, Domain e1 ], e2) ->
      let e1, rt1 = expr cx e1 in
      let v, cx = adj cx v XSet in
      let e2, rt2 = expr cx e2 in
      let op = opq_from_smb (T.Uver (T.Fcn (TUnknown, TUnknown))) in
      (Apply (op, [ maybe_cast rt1 e1 ; Lambda ([ v, Shape_expr ], maybe_cast rt2 e2) %% [] ]) @@ oe, RSet)

  | FcnApp (e1, [ e2 ]) ->
      let e1, rt1 = expr cx e1 in
      let e2, rt2 = expr cx e2 in
      let op = opq_from_smb (T.Uver (T.FcnApp (TUnknown, TUnknown))) in
      (Apply (op, [ maybe_cast rt1 e1 ; maybe_cast rt2 e2 ]) @@ oe, RSet)

  | Arrow (e1, e2) ->
      let e1, rt1 = expr cx e1 in
      let e2, rt2 = expr cx e2 in
      let op = opq_from_smb (T.Uver (T.Arrow (TUnknown, TUnknown))) in
      (Apply (op, [ maybe_cast rt1 e1 ; maybe_cast rt2 e2 ]) @@ oe, RSet)

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

  | Num (s, "") when !Params.enc_arith ->
      let smb = T.Ucast (TAtom TInt) in
      let op = opq_from_smb smb in
      (Apply (op, [ oe ]) %% [], RSet)

  | Num (s, "") ->
      let smb = T.Uver (T.IntLit (int_of_string s)) in
      let op = opq_from_smb smb in
      (op $$ oe, RSet)

  | String s->
      let smb = T.Uver (T.StrLit s) in
      let op = opq_from_smb smb in
      (op $$ oe, RSet)

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

  | Internal (B.TRUE | B.FALSE) ->
      let e, rt = expr cx op in
      (e $$ op, XOp ([], rt))

  | Internal b ->
      let smb =
        match b with
        | B.STRING    -> T.Uver T.Strings
        | B.BOOLEAN   -> T.Uver T.Booleans
        | B.SUBSET    -> T.Uver (T.Subset TUnknown)
        | B.UNION     -> T.Uver (T.Union TUnknown)
        | B.DOMAIN    -> T.Uver (T.Domain (TUnknown, TUnknown))
        | B.Subseteq  -> T.Uver (T.SubsetEq TUnknown)
        | B.Mem       -> T.Uver (T.Mem TUnknown)
        | B.Setminus  -> T.Uver (T.SetMinus TUnknown)
        | B.Cap       -> T.Uver (T.Cap TUnknown)
        | B.Cup       -> T.Uver (T.Cup TUnknown)

        | B.Nat       -> T.Uver T.Nats
        | B.Int       -> T.Uver T.Ints
        | B.Real      -> T.Uver T.Reals
        | B.Plus      -> T.Uver T.Plus
        | B.Uminus    -> T.Uver T.Uminus
        | B.Minus     -> T.Uver T.Minus
        | B.Times     -> T.Uver T.Times
        | B.Ratio     -> T.Uver T.Ratio
        | B.Quotient  -> T.Uver T.Quotient
        | B.Remainder -> T.Uver T.Remainder
        | B.Exp       -> T.Uver T.Exp
        | B.Range     -> T.Uver T.Range
        | B.Lteq      -> T.Uver T.Lteq

        | B.Infinity
        | B.Lt
        | B.Gteq
        | B.Gt
        | B.Divides ->
            error ~at:op "Unexpected arithmetic builtin"


        | B.Prime
        | B.StrongPrime
        | B.Leadsto
        | B.ENABLED
        | B.UNCHANGED
        | B.Cdot
        | B.Actplus
        | B.Box _
        | B.Diamond ->
            error ~at:op "Unexpected modal builtin"

        | B.Seq
        | B.Len
        | B.BSeq
        | B.Cat
        | B.Append
        | B.Head
        | B.Tail
        | B.SubSeq
        | B.SelectSeq ->
            error ~at:op "Unexpected sequences builtin"

        | B.OneArg
        | B.Extend
        | B.Print
        | B.PrintT
        | B.Assert
        | B.JavaTime
        | B.TLCGet
        | B.TLCSet
        | B.Permutations
        | B.SortSeq
        | B.RandomElement
        | B.Any
        | B.ToString ->
            error ~at:op "Unexpected TLC builtin"

        | B.Unprimable
        | B.Irregular ->
            error ~at:op "Unexpected special builtin"

        | _ ->
            error ~at:op "Unexpected builtin"
      in
      let op = opq_from_smb smb in
      let sch = T.get_sch (T.std_smb smb) in
      let xt = from_sch sch in
      (op, xt)

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
      (* FIXME This is a hack
       * (get Direct to ignore type annotations in axioms) *)
      let v, cx =
        if has v Props.type_prop then
          let _, cx = adj cx v XSet in
          v, cx
        else
          adj cx v XSet
      in
      (*let v, cx = adj cx v XSet in*)
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
  | Fresh (v, shp, k, Unbounded) when has v Props.targ_prop ->
      (* FIXME hack *)
      let arg = get v Props.targ_prop in
      let xty =
        from_arg arg |> function
          | ASet -> XSet
          | AOp (n, rt) -> XOp (List.init n (fun _ -> ASet), rt)
      in
      let v, cx = adj cx v xty in
      (cx, Fresh (v, shp, k, Unbounded) @@ h)

  | Fresh (v, shp, k, d) ->
      let d =
        match d with
        | Bounded (e, Visible) ->
            let e, rt = expr cx e in
            Bounded (maybe_cast rt e, Visible)
        | _ -> d
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

  | Defn (df, wd, Visible, ex) ->
      let cx, df = defn cx df in
      (cx, Defn (df, wd, Visible, ex) @@ h)

  | Defn ({ core = Operator (v, ({core = Lambda ([_],_)} as op)) } as df, User, Hidden, ex)
  when v.core = N_hints.with_id ->
      let xt = XOp ([ ASet ], RForm) in
      let v, cx = adj cx v xt in
      (cx, Defn (Operator (v, op) @@ df, User, Hidden, ex) @@ h)

  | Defn (df, wd, Hidden, ex) ->
      (* NOTE Need to update df with a type annotation *)
      let cx, df =
        begin match df.core with
        | Operator (v, ({ core = Lambda (xs, _) } as op)) ->
            let xt = XOp (
              List.map begin function
                | _, Shape_expr -> ASet
                | _, Shape_op n -> AOp (n, RSet)
              end xs, RSet)
            in
            let v, cx = adj cx v xt in
            (cx, Operator (v, op) @@ df)
        | Operator (v, e) ->
            let xt = XSet in
            let v, cx = adj cx v xt in
            (cx, Operator (v, e) @@ df)
        | _ ->
            error ~at:df "Not implemented"
        end
      in
      (cx, Defn (df, wd, Hidden, ex) @@ h)

  | Fact (e, Visible, tm) ->
      let e, rt = expr cx e in
      let cx = bump cx in
      (cx, Fact (maybe_proj rt e, Visible, tm) @@ h)

  | Fact (_, Hidden, _) ->
      let cx = bump cx in
      (cx, h)

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

