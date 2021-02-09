(*
 * encode/standardize.ml
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
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
  Errors.bug ?at mssg


(* {3 Helpers} *)

let adj scx h =
  Type.Visit.adj scx h

let mk_opq smb =
  let op = Opaque (get_name smb) %% [] in
  let op = assign op smb_prop smb in
  op


(* {3 Main} *)

(* TODO Implement typelvl=1 *)

(* NOTE This module does not perform type inference, it only works
 * from the type annotations it can find. *)

let visitor = object (self : 'self)
  inherit [unit, s] Expr.Visit.foldmap as super

  method expr scx s oe =
    if has oe Props.icast_prop then
      let ty0 = get oe Props.icast_prop in
      let s, oe = self#expr scx s (remove oe Props.icast_prop) in
      let s, smb = mk_smb s (Cast ty0) in
      let opq = mk_opq smb in
      (s, Apply (opq, [ oe ]) %% [])

    else if has oe Props.bproj_prop then
      let ty0 = get oe Props.bproj_prop in
      let s, oe = self#expr scx s (remove oe Props.bproj_prop) in
      let s, smb = mk_smb s (True ty0) in
      let opq = mk_opq smb in
      let op = assign (Internal B.Eq %% []) Props.tpars_prop [ ty0 ] in
      (s, Apply (op, [ oe ; opq ]) %% [])
    else

    begin match oe.core with

    | Internal (B.TRUE | B.FALSE
               | B.Implies | B.Equiv | B.Conj | B.Disj
               | B.Neg | B.Eq | B.Neq
               | B.Unprimable | B.Irregular) ->
        (* Ignored builtins *)
        (s, oe)

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

          | Plus,       Some [ TAtm TAInt ]   -> TIntPlus
          | Uminus,     Some [ TAtm TAInt ]   -> TIntUminus
          | Minus,      Some [ TAtm TAInt ]   -> TIntMinus
          | Times,      Some [ TAtm TAInt ]   -> TIntTimes
          | Exp,        Some [ TAtm TAInt ]   -> TIntExp
          | Quotient,   Some [ ]              -> TIntQuotient
          | Remainder,  Some [ ]              -> TIntRemainder
          | Lteq,       Some [ ]              -> TIntLt
          | Lt,         Some [ ]              -> TIntLteq
          | Gteq,       Some [ ]              -> TIntGt
          | Gt,         Some [ ]              -> TIntGteq
          | Range,      Some [ ]              -> TIntRange

          | _,      Some _      ->
              error ~at:oe "Typelvl=1 not implemented"
          | _, _ ->
              error ~at:oe "Unexpected builtin"
        in
        let s, smb = mk_smb s tla_smb in
        (s, mk_opq smb)

    | Choose (v, Some dom, e) ->
        error ~at:oe "Unsupported bounded choose-expression"
    | Choose (v, None, e) ->
        let h = Fresh (v, Shape_expr, Constant, Unbounded) %% [] in
        let scx = adj scx h in
        let s, e = self#expr scx s e in
        if has oe Props.tpars_prop then
          error ~at:oe "Typelvl=1 not implemented"
        else
          let s, smb = mk_smb s Choose in
          let opq = mk_opq smb in
          (s, Apply (opq, [ Lambda ([ v, Shape_expr ], e) %% [] ]) @@ oe)

    | SetEnum es ->
        let s, es =
          List.fold_left begin fun (s, r_es) e ->
            let s, e = self#expr scx s e in
            (s, e :: r_es)
          end (s, []) es |>
          fun (s, r_es) -> (s, List.rev r_es)
        in
        if has oe Props.tpars_prop then
          error ~at:oe "Typelvl=1 not implemented"
        else
          let n = List.length es in
          let s, smb = mk_smb s (SetEnum n) in
          let opq = mk_opq smb in
          (s, Apply (opq, es) @@ oe)

    | SetSt (v, e1, e2) ->
        let s, e1 = self#expr scx s e1 in
        let h = Fresh (v, Shape_expr, Constant, Bounded (e1, Visible)) %% [] in
        let scx = adj scx h in
        let s, e2 = self#expr scx s e2 in
        if has oe Props.tpars_prop then
          error ~at:oe "Typelvl=1 not implemented"
        else
          let s, smb = mk_smb s SetSt in
          let opq = mk_opq smb in
          (s, Apply (opq, [ e1 ; Lambda ([ v, Shape_expr ], e2) %% [] ]) %% [])

    | SetOf (e, bs) ->
        let scx, s, bs = self#bounds scx s bs in
        let s, e = self#expr scx s e in
        if has oe Props.tpars_prop then
          error ~at:oe "Typelvl=1 not implemented"
        else
          let n = List.length bs in
          let s, smb = mk_smb s (SetOf n) in
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
          (s, Apply (opq, (ds @ [ Lambda (bs, e) %% [] ])) %% [])

    | String str ->
        if has oe Props.tpars_prop then
          error ~at:oe "Typelvl=1 not implemented"
        else
          let s, smb = mk_smb s (StrLit str) in
          let opq = mk_opq smb in
          (s, opq)

    | Num (m, "") ->
        if has oe Props.tpars_prop then
          error ~at:oe "Literal numbers not implemented"
        else
          let n = int_of_string m in
          let s, smb = mk_smb s (IntLit n) in
          let opq = mk_opq smb in
          (s, opq)

    | Arrow (e1, e2) ->
        let s, e1 = self#expr scx s e1 in
        let s, e2 = self#expr scx s e2 in
        if has oe Props.tpars_prop then
          error ~at:oe "Typelvl=1 not implemented"
        else
          let s, smb = mk_smb s FunSet in
          let opq = mk_opq smb in
          (s, Apply (opq, [ e1 ; e2 ]) %% [])

    | Fcn (bs, _) when List.length bs <> 1 ->
        error ~at:oe "Unsupported multi-arguments function"
    | Fcn ([ v, Constant, Domain (e1) ], e2) ->
        let s, e1 = self#expr scx s e1 in
        let h = Fresh (v, Shape_expr, Constant, Bounded (e1, Visible)) %% [] in
        let scx = adj scx h in
        let s, e2 = self#expr scx s e2 in
        if has oe Props.tpars_prop then
          error ~at:oe "Typelvl=1 not implemented"
        else
          let s, smb = mk_smb s FunConstr in
          let opq = mk_opq smb in
          (s, Apply (opq, [ e1 ; Lambda ([ v, Shape_expr ], e2) %% [] ]) %% [])

    | FcnApp (_, es) when List.length es <> 1 ->
        error ~at:oe "Unsupported multi-arguments application"
    | FcnApp (e1, [ e2 ]) ->
        let s, e1 = self#expr scx s e1 in
        let s, e2 = self#expr scx s e2 in
        if has oe Props.tpars_prop then
          error ~at:oe "Typelvl=1 not implemented"
        else
          let s, smb = mk_smb s FunApp in
          let opq = mk_opq smb in
          (s, Apply (opq, [ e1 ; e2 ]) %% [])

    | _ -> super#expr scx s oe

    end |>
    fun (s, e) ->
      if has e pattern_prop then begin
        let pats = get e pattern_prop in
        let s, pats =
          List.fold_left begin fun (s, r_pats) pat ->
            let s, pat =
              List.fold_left begin fun (s, r_es) e ->
                let s, e = self#expr scx s e in
                (s, e :: r_es)
              end (s, []) pat |>
              fun (s, r_es) -> (s, List.rev r_es)
            in
            (s, pat :: r_pats)
          end (s, []) pats |>
          fun (s, r_pats) -> (s, List.rev r_pats)
        in
        (s, add_patterns (remove_patterns e) pats)
      end else
        (s, e)

end


let main sq =
  let cx = ((), Deque.empty) in
  let s = init in
  let _, _, sq = visitor#sequent cx s sq in
  sq

