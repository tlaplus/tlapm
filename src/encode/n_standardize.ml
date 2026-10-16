(*
 * encode/standardize.ml
 *
 *
 * Copyright (C) 2022  INRIA and Microsoft Corporation
 *)

open Ext
open Property
open Expr.T
open Type.T

open N_table
open N_smb

module B = Builtin


let error ?at mssg =
  let mssg = "Encode.Standardize: " ^ mssg in
  (*Errors.bug ?at mssg*)
  failwith mssg


(* {3 Helpers} *)

let adj scx h =
  Expr.Visit.adj scx h

let mk_opq smb =
  let op = Opaque (get_name smb) %% [] in
  let op = assign op smb_prop smb in
  op

let err_count = ref 0

let is_set e =
  match e.core with
  | Apply ({ core = Opaque s } as op, _) when has op smb_prop ->
      let smb = get op smb_prop in
      begin match get_defn smb with
      | SetEnum _ | Union | Subset | Cup | Cap | SetMinus | SetSt
      | SetOf _ | BoolSet | StrSet | IntSet | NatSet | IntRange | FunSet
      | Product _ | RecSet _ | SeqSeq ->
          true
      | _ -> false
      end
  | _ -> false


(* Lower [CASE p1 -> e1 [] ... [] pn -> en [] OTHER -> oth] to IF/ite.
 *
 * Semantics (tlaplus/tlapm#304).  A CASE denotes
 *     CHOOSE v : (p1 /\ v = e1) \/ ... \/ (pn /\ v = en)
 *                \/ (~p1 /\ ... /\ ~pn /\ v = oth)
 * (Specifying Systems, Sec. 16.1.4; isabelle/CaseExpressions.thy).  Arms are
 * unordered: if several guards hold, the value is one of their results, but
 * which one is unspecified.  Lowering to the ordered
 *     IF p1 THEN e1 ELSE IF p2 THEN e2 ELSE ... oth
 * is therefore unsound: it wrongly proves that the first enabled arm wins,
 * e.g. [(CASE TRUE -> 1 [] TRUE -> 2) = 1], which TLA+ does not entail.
 *
 * Encoding.  Each arm but the last gets an oracle, an uninterpreted Boolean
 * function [case_choice_n_i] (n arms, arm i).  Arm i is selected iff the
 * IF-chain reaches it and
 *     p_i /\ (oracle_i \/ ~(p_{i+1} \/ ... \/ p_n))
 * i.e. its guard holds and either the oracle picks it or no later arm could
 * be picked instead.  The last arm needs no oracle.  For three arms:
 *     IF p1 /\ (o1 \/ ~(p2 \/ p3)) THEN e1
 *     ELSE IF p2 /\ (o2 \/ ~p3) THEN e2
 *     ELSE IF p3 THEN e3
 *     ELSE oth
 *
 * The oracles act as an arbiter between overlapping arms.  oracle_i only
 * matters when arm i and some later arm are both enabled: it decides
 * whether arm i wins or defers to a later arm.  The winner is thus the
 * first enabled arm whose oracle accepts, or else the last enabled arm.
 * The oracles are uninterpreted, so a proof cannot rely on how they
 * decide, i.e., on which overlapping arm wins.  Since they decide from
 * the guards and results alone, the same CASE always gets the same
 * decision.
 *
 * Example.  Every oracle takes all guards followed by all results; oracles
 * of different arms differ only in their name.  With x \in Int,
 *     CASE x > 0 -> 1 [] x > 5 -> 2 [] x < 10 -> 3
 * has overlapping arms (all three hold at x = 7, the first and the third
 * at x = 3) and becomes
 *     IF x > 0 /\ (o1(A) \/ ~(x > 5 \/ x < 10)) THEN 1
 *     ELSE IF x > 5 /\ (o2(A) \/ ~(x < 10)) THEN 2
 *     ELSE IF x < 10 THEN 3
 *     ELSE oth
 * where A is the argument list (x > 0, x > 5, x < 10, 1, 2, 3).  Since A
 * mentions x, the oracles may decide differently for different x: at x = 7
 * they see (TRUE, TRUE, TRUE, 1, 2, 3), at x = 3 (TRUE, FALSE, TRUE, 1, 2, 3).
 * The same CASE over y uses the same oracles applied to y's arguments, so
 * given x = y the solver proves both CASEs equal.  With the arms permuted,
 *     CASE x > 5 -> 2 [] x > 0 -> 1 [] x < 10 -> 3
 * the oracles see (x > 5, x > 0, x < 10, 2, 1, 3) instead; as the arms
 * overlap, the solver cannot relate this CASE to the original, although
 * TLA+ considers them equal.
 *
 * What the solver can derive:
 * - If exactly one guard holds, that arm is selected whatever the oracles,
 *   as with the ordered IF; disjoint CASEs behave as before.
 * - If no guard holds, the value is [oth].
 * - Every branch requires its own guard, so the value is always the result
 *   of an enabled arm, e.g. [(CASE TRUE -> 1 [] TRUE -> 2) \in {1, 2}].
 * - Which overlapping arm is selected depends on the oracles, about which
 *   nothing is known; neither the first nor the last arm can be proved.
 *
 * Why oracles.  Encoding a CASE as an opaque term would be sound but would
 * lose disjoint and OTHER cases, the common use in specs.  Keeping the
 * ordered IF only for disjoint guards is not an option either: whether the
 * guards are disjoint usually depends on hypotheses, which only the solver
 * sees.  With oracles, the solver proves everything it proved with the
 * ordered IF, minus the false proofs.
 *
 * Soundness.  Whatever value v the CHOOSE picks, interpreting oracle_i as
 * [e_i = v] makes the IF-chain select v: the first enabled arm whose result
 * is v is selected, as every earlier enabled arm has a different result.
 * The CHOOSE'n value depends only on the set of enabled results, hence on
 * the guards and results, so this interpretation is a function of the
 * oracle's arguments ([oth] only matters when no guard holds).  Oracles with 
 * fewer arguments would be unsound, e.g. with
 *     C(x) == CASE TRUE -> x [] TRUE -> 0
 * and a constant oracle, the solver could prove
 *     [(\A x : C(x) = x) \/ (\A x : C(x) = 0)]
 * whereas the CHOOSE may pick x for some x and 0 for others.
 *
 * Completeness.  Repeated occurrences of one CASE, e.g. in a hypothesis and
 * in the goal, must be provably equal.  Hence the oracle symbol depends
 * only on the number of arms, the arm index, and the result type, and is
 * shared by all CASEs of that shape.  Sharing is sound, because CASEs whose
 * guards and results agree have the same set of enabled results, hence the
 * same CHOOSE'n value.
 *
 * Sharing does not give full completeness.  CHOOSE picks the same value for
 * equivalent predicates, so CASEs with the same set of enabled results are
 * equal.  The encoding relates two CASEs only if they have the same number
 * of arms and agree arm by arm: CASEs that differ in arm count use
 * different oracles, and
 * permuting arms reorders the oracles' arguments, as in the example.
 * The solver can then prove such CASEs equal only if no arms overlap, e.g.
 * neither
 *     (CASE p -> "u" [] q -> "v") = (CASE p -> "u" [] q -> "v" [] p -> "u")
 * nor
 *     (CASE p -> x [] q -> y [] OTHER -> z)
 *         = (CASE q -> y [] p -> x [] OTHER -> z)
 * Zenon has the same limitation.  Isabelle, which reasons about the CHOOSE
 * itself, proves the former automatically but not the latter. *)
let lower_case ty0 ps oth =
  let n = List.length ps in
  let cs, es = List.split ps in
  (* Oracle signature: n Booleans (the guards) and n values of the result
   * type (the results), returning a Boolean. *)
  let ty1s =
    List.map (fun _ -> Ty1 ([], TAtm TABol)) cs
    @ List.map (fun _ -> Ty1 ([], ty0)) es
  in
  (* Symbols are identified by name, so the name must determine the
   * signature: the arity is fixed by [n], the argument and result types by
   * [ty0]. *)
  let oracle i =
    let s =
      "case_choice_" ^ string_of_int n ^ "_" ^ string_of_int i
      ^ "_" ^ ty_to_string ty0
    in
    let smb = mk_smb (Anon (s, Ty2 (ty1s, TAtm TABol))) in
    Apply (mk_opq smb, cs @ es) %% []
  in
  let mk_if c e f = assign (If (c, e, f) %% []) Props.tpars_prop [ ty0 ] in
  (* [spin i ps] encodes arms [i..n], given as [ps]. *)
  let rec spin i = function
    | [] -> oth
    | [ (c, e) ] -> mk_if c e oth
    | (c, e) :: ps ->
        let later = List (Or, List.map fst ps) %% [] in
        let none_later = Apply (Internal B.Neg %% [], [ later ]) %% [] in
        let c = List (And, [ c ; List (Or, [ oracle i ; none_later ]) %% [] ]) %% [] in
        mk_if c e (spin (i + 1) ps)
  in
  spin 1 ps


(* {3 Main} *)

(* NOTE This module does not perform type inference, it only works
 * from the type annotations it can find. *)

let visitor = object (self : 'self)
  inherit [unit] Expr.Visit.map as super

  method expr scx oe =
    if has oe Props.icast_prop then
      let ty0 = get oe Props.icast_prop in
      let oe = self#expr scx (remove oe Props.icast_prop) in
      let smb = mk_smb (Cast ty0) in
      let opq = mk_opq smb in
      Apply (opq, [ oe ]) %% []

    else if has oe Props.sproj_prop then
      let ty0 = get oe Props.sproj_prop in
      let oe = self#expr scx (remove oe Props.sproj_prop) in
      let smb = mk_smb (Proj ty0) in
      let opq = mk_opq smb in
      Apply (opq, [ oe ]) %% []

    else if has oe Props.bproj_prop then
      let ty0 = get oe Props.bproj_prop in
      let oe = self#expr scx (remove oe Props.bproj_prop) in
      let smb = mk_smb (True ty0) in
      let opq = mk_opq smb in
      let op = assign (Internal B.Eq %% []) Props.tpars_prop [ ty0 ] in
      Apply (op, [ oe ; opq ]) %% []
    else

    begin match oe.core with

    (* FIXME Rewriting may add this special primitive in expressions *)
    | Apply ({ core = Opaque "IsAFcn" } as op, [ e ]) ->
        let e = self#expr scx e in
        let smb = mk_smb FunIsafcn in
        let opq = mk_opq smb $$ op in
        Apply (opq, [ e ]) @@ oe

    | Opaque s ->
        let ty2 = Ty2 ([], TAtm TAIdv) in
        let s = "OPAQUE_" ^ s in
        let smb = mk_smb (Anon (s, ty2)) in
        let opq = mk_opq smb $$ oe in
        opq
    | Apply ({ core = Opaque s } as op, es) ->
        let es = List.map (self#expr scx) es in
        let ty1 = Ty1 (List.map (fun _ -> TAtm TAIdv) es, TAtm TAIdv) in
        let smb = mk_smb (Anon (s, upcast_ty2 ty1)) in
        let opq = mk_opq smb $$ op in
        Apply (opq, es) @@ oe

    | Internal (B.TRUE | B.FALSE
               | B.Implies | B.Equiv | B.Conj | B.Disj
               | B.Neg | B.Eq | B.Neq
               | B.Unprimable | B.Irregular) ->
        (* Ignored builtins *)
        oe

    | Internal b ->
        let tla_smb =
          match b, query oe Props.tpars_prop with
          | Mem,        None      -> Mem
          | Subseteq,   None      -> SubsetEq
          | UNION,      None      -> Union
          | SUBSET,     None      -> Subset
          | Cup,        None      -> Cup
          | Cap,        None      -> Cap
          | Setminus,   None      -> SetMinus
          | BOOLEAN,    None      -> BoolSet
          | STRING,     None      -> StrSet
          | Int,        None      -> IntSet
          | Nat,        None      -> NatSet
          | Plus,       None      -> IntPlus
          | Uminus,     None      -> IntUminus
          | Minus,      None      -> IntMinus
          | Times,      None      -> IntTimes
          | Exp,        None      -> IntExp
          | Quotient,   None      -> IntQuotient
          | Remainder,  None      -> IntRemainder
          | Lteq,       None      -> IntLteq
          | Lt,         None      -> IntLt
          | Gteq,       None      -> IntGteq
          | Gt,         None      -> IntGt
          | Range,      None      -> IntRange
          | DOMAIN,     None      -> FunDom
          | Seq,        None      -> SeqSeq
          | Len,        None      -> SeqLen
          | BSeq,       None      -> SeqBSeq
          | Cat,        None      -> SeqCat
          | Append,     None      -> SeqAppend
          | Head,       None      -> SeqHead
          | Tail,       None      -> SeqTail
          | SubSeq,     None      -> SeqSubSeq
          | SelectSeq,  None      -> SeqSelectSeq

          | Plus,       Some [ TAtm TAInt ]   -> TIntPlus
          | Uminus,     Some [ TAtm TAInt ]   -> TIntUminus
          | Minus,      Some [ TAtm TAInt ]   -> TIntMinus
          | Times,      Some [ TAtm TAInt ]   -> TIntTimes
          (*| Exp,        Some [ TAtm TAInt ]   -> TIntExp*)
          | Quotient,   Some [ ]              -> TIntQuotient
          | Remainder,  Some [ ]              -> TIntRemainder
          | Lteq,       Some [ TAtm TAInt ]   -> TIntLteq
          | Lt,         Some [ TAtm TAInt ]   -> TIntLt
          | Gteq,       Some [ TAtm TAInt ]   -> TIntGteq
          | Gt,         Some [ TAtm TAInt ]   -> TIntGt

          | (Plus | Uminus | Minus | Times | Exp | Lteq | Lt | Gteq | Gt),
                        Some [ TAtm TARel ]   ->
              error ~at:oe "Real numbers not implemented"
          | _,          Some _      ->
              error ~at:oe "unexpected type annotation"
          | _, _ ->
              let mssg = "Unexpected builtin '" ^
                         B.builtin_to_string b ^ "'"
              in
              error ~at:oe mssg
        in
        let smb = mk_smb tla_smb in
        mk_opq smb

    | Choose (v, Some dom, e) ->
        error ~at:oe "Unsupported bounded choose-expression"
    | Choose (v, None, e) ->
        let h = Fresh (v, Shape_expr, Constant, Unbounded) %% [] in
        let scx = adj scx h in
        let e = self#expr scx e in
        if has oe Props.tpars_prop then
          error ~at:oe "unexpected type annotation"
        else
          let smb = mk_smb Choose in
          let opq = mk_opq smb in
          Apply (opq, [ Lambda ([ v, Shape_expr ], e) %% [] ]) @@ oe

    | SetEnum es ->
        let es =
          List.fold_left begin fun (r_es) e ->
            let e = self#expr scx e in
            (e :: r_es)
          end ([]) es |>
          fun (r_es) -> (List.rev r_es)
        in
        if has oe Props.tpars_prop then
          error ~at:oe "T1 not implemented"
        else
          let n = List.length es in
          let smb = mk_smb (SetEnum n) in
          let opq = mk_opq smb in
          Apply (opq, es) @@ oe

    | SetSt (v, e1, e2) ->
        let e1 = self#expr scx e1 in
        let h = Fresh (v, Shape_expr, Constant, Bounded (e1, Visible)) %% [] in
        let scx = adj scx h in
        let e2 = self#expr scx e2 in
        if has oe Props.tpars_prop then
          error ~at:oe "unexpected type annotation"
        else
          let smb = mk_smb SetSt in
          let opq = mk_opq smb in
          Apply (opq, [ e1 ; Lambda ([ v, Shape_expr ], e2) %% [] ]) %% []

    | SetOf (e, bs) ->
        let scx, bs = self#bounds scx bs in
        let e = self#expr scx e in
        if has oe Props.tpars_prop then
          error ~at:oe "unexpected type annotation"
        else
          let n = List.length bs in
          let smb = mk_smb (SetOf n) in
          let opq = mk_opq smb in
          let ds, bs =
            List.fold_left begin fun (r_ds, r_bs, last) (v, _, dom) ->
              match dom, last with
              | Domain d, _
              | Ditto, Some d ->
                  (d :: r_ds, (v, Shape_expr) :: r_bs, Some d)
              | _, _ ->
                  error ~at:v "Missing domain on bound"
            end ([], [], None) bs |>
            fun (r_ds, r_bs, _) ->
              (List.rev r_ds, List.rev r_bs)
          in
          Apply (opq, (ds @ [ Lambda (bs, e) %% [] ])) %% []

    | String str ->
        let smb = mk_smb (StrLit str) in
        let opq = mk_opq smb in
        opq

    | Num (m, "") ->
        if has oe Props.tpars_prop then
          let n = int_of_string m in
          let smb = mk_smb (TIntLit n) in
          let opq = mk_opq smb in
          opq
        else
          let n = int_of_string m in
          let smb = mk_smb (IntLit n) in
          let opq = mk_opq smb in
          opq

    | Arrow (e1, e2) ->
        let e1 = self#expr scx e1 in
        let e2 = self#expr scx e2 in
        if has oe Props.tpars_prop then
          error ~at:oe "unexpected type annotation"
        else
          let smb = mk_smb FunSet in
          let opq = mk_opq smb in
          Apply (opq, [ e1 ; e2 ]) %% []

    | Fcn (bs, _) when List.length bs <> 1 ->
        error ~at:oe "Unsupported multi-arguments function"
    | Fcn ([ v, Constant, Domain (e1) ], e2) ->
        let e1 = self#expr scx e1 in
        let h = Fresh (v, Shape_expr, Constant, Bounded (e1, Visible)) %% [] in
        let scx = adj scx h in
        let e2 = self#expr scx e2 in
        if has oe Props.tpars_prop then
          error ~at:oe "unexpected type annotation"
        else
          let smb = mk_smb FunConstr in
          let opq = mk_opq smb in
          Apply (opq, [ e1 ; Lambda ([ v, Shape_expr ], e2) %% [] ]) %% []

    | FcnApp (_, es) when List.length es <> 1 ->
        error ~at:oe "Unsupported multi-arguments application"
    | FcnApp (e1, [ e2 ]) ->
        let e1 = self#expr scx e1 in
        let e2 = self#expr scx e2 in
        if has oe Props.tpars_prop then
          error ~at:oe "unexpected type annotation"
        else
          let smb = mk_smb FunApp in
          let opq = mk_opq smb in
          Apply (opq, [ e1 ; e2 ]) %% []

    | Except (e1, [ [ Except_apply e2 ], e3 ]) ->
        let e1 = self#expr scx e1 in
        let e2 = self#expr scx e2 in
        let e3 = self#expr scx e3 in
        if has oe Props.tpars_prop then
          error ~at:oe "unexpected type annotation"
        else
          let smb = mk_smb FunExcept in
          let opq = mk_opq smb in
          Apply (opq, [ e1 ; e2 ; e3 ]) %% []
    | Except (e1, [ [ Except_dot s ], e3 ]) ->
        let e1 = self#expr scx e1 in
        let e3 = self#expr scx e3 in
        if has oe Props.tpars_prop then
          error ~at:oe "unexpected type annotation"
        else
          let smb = mk_smb FunExcept in
          let opq = mk_opq smb in
          let strlit = mk_smb (StrLit s) in
          let strlit_opq = mk_opq strlit in
          Apply (opq, [ e1 ; strlit_opq  ; e3 ]) %% []

    | Except _ ->
        error ~at:oe "Unsupported EXCEPT expression"

    | Tuple es ->
        let es = List.map (self#expr scx) es in
        if has oe Props.tpars_prop then
          error ~at:oe "unexpected type annotation"
        else
          let n = List.length es in
          let smb = mk_smb (Tuple n) in
          let opq = mk_opq smb in
          Apply (opq, es) %% []

    | Product es ->
        let es = List.map (self#expr scx) es in
        if has oe Props.tpars_prop then
          error ~at:oe "unexpected type annotation"
        else
          let n = List.length es in
          let smb = mk_smb (Product n) in
          let opq = mk_opq smb in
          Apply (opq, es) %% []

    | Record fs ->
        let fs = List.map (fun (f, e) -> (f, self#expr scx e)) fs in
        if has oe Props.tpars_prop then
          error ~at:oe "unexpected type annotation"
        else
          let fs, es = List.split fs in
          let smb = mk_smb (Rec fs) in
          let opq = mk_opq smb in
          Apply (opq, es) %% []

    | Rect fs ->
        let fs = List.map (fun (f, e) -> (f, self#expr scx e)) fs in
        if has oe Props.tpars_prop then
          error ~at:oe "unexpected type annotation"
        else
          let fs, es = List.split fs in
          let smb = mk_smb (RecSet fs) in
          let opq = mk_opq smb in
          Apply (opq, es) %% []

    | Dot (e, s) ->
        let e = self#expr scx e in
        if has oe Props.tpars_prop then
          error ~at:oe "unexpected type annotation"
        else
          let smb = mk_smb FunApp in
          let opq = mk_opq smb in
          let strlit = mk_smb (StrLit s) in
          let strlit_opq = mk_opq strlit in
          Apply (opq, [ e ; strlit_opq ]) %% []

    | Case (ps, oth) ->
        let ps =
          List.map begin fun (p, e) ->
            (self#expr scx p, self#expr scx e)
          end ps
        in
        let ty0 =
          match get oe Props.tpars_prop with
          | [ ty0 ] -> ty0
          | _ -> error ~at:oe "Bad type annotation"
        in
        let oth =
          match oth with
          | Some o -> self#expr scx o
          | None ->
              incr err_count;
              let err = "incomplete_case_error_" ^ string_of_int !err_count in
              let smb = mk_smb (Anon (err, Ty2 ([], ty0))) in
              mk_opq smb
        in
        (lower_case ty0 ps oth).core @@ oe

    | _ -> super#expr scx oe

    end |>
    map_pats (List.map (self#expr scx))

  method hyp scx h =
    match h.core with
    | Defn (_, _, Hidden, _)
    | Fact (_, Hidden, _) ->
        let scx = adj scx h in
        (scx, h)
    | _ -> super#hyp scx h

end


(* For SMT, we also replace equalities by uninterpreted symbols to permit
   additional trigger instantiations *)

type pol =
  | Positive
  | Negative
  | Neither

let inv = function
  | Positive -> Negative
  | Negative -> Positive
  | Neither -> Neither

let set_extensionality_visitor = object (self : 'self)
  inherit [pol] Expr.Visit.map as super

  method expr (pol, hx as scx) oe =
    match oe.core with
    | Apply ({ core = Internal B.Eq } as op, [ e ; f ])
      when ((pol = Positive) || (pol = Neither))
        && (match query op Props.tpars_prop with
            | Some [ TSet _ ] -> true
            | _ -> is_set e || is_set f) ->
        let e = self#expr scx e in
        let f = self#expr scx f in
        let ty0 =
          match query op Props.tpars_prop with
          | Some [ TSet ty0 ] -> TSet ty0
          | _ -> TSet (TAtm TAIdv)
        in
        let smb = mk_smb (ExtTrigEq ty0) in
        let opq = mk_opq smb $$ op in
        Apply (opq, [ e ; f ]) @@ oe

    | Apply ({ core = Internal B.Neq } as op, [ e ; f ])
      when ((pol = Negative) || (pol = Neither))
        && (match query op Props.tpars_prop with
            | Some [ TSet _ ] -> true
            | _ -> is_set e || is_set f) ->
        let e = self#expr scx e in
        let f = self#expr scx f in
        let ty0 =
          match query op Props.tpars_prop with
          | Some [ TSet ty0 ] -> TSet ty0
          | _ -> TSet (TAtm TAIdv)
        in
        let smb = mk_smb (ExtTrigEq ty0) in
        let opq = mk_opq smb $$ op in
        Apply (Internal B.Neg %% [],
          [ Apply (opq, [ e ; f ]) %% [] ]) @@ oe

    | Apply ({ core = Internal B.Implies } as op, [ e ; f ]) ->
        let e = self#expr (inv pol, hx) e in
        let f = self#expr scx f in
        Apply (op, [ e ; f ]) @@ oe

    | Apply ({ core = Internal (B.Conj | B.Disj) } as op, [ e ; f ]) ->
        let e = self#expr (pol, hx) e in
        let f = self#expr (pol, hx) f in
        Apply (op, [ e ; f ]) @@ oe

    | Apply ({ core = Internal B.Neg } as op, [ e ]) ->
        let e = self#expr (inv pol, hx) e in
        Apply (op, [ e ]) @@ oe

    | Apply (op, es) ->
        let es = List.map (self#expr (Neither, hx)) es in
        Apply (op, es) @@ oe

    | _ -> super#expr scx oe

  method sequent (pol, hx) sq =
    let (_, hx), hs = self#hyps (inv pol, hx) sq.context in
    let e = self#expr (pol, hx) sq.active in
    (pol, hx), { context = hs ; active = e }
end


let main ?(smt_set_extensionality=false) sq =
  let cx = ((), Deque.empty) in
  let _, sq = visitor#sequent cx sq in

  if smt_set_extensionality then
    snd (set_extensionality_visitor#sequent (Positive, Deque.empty) sq)
  else
    sq

