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
  (*Errors.bug ?at mssg*)
  failwith mssg


(* {3 Helpers} *)

let adj scx h =
  Expr.Visit.adj scx h

let mk_opq smb =
  let op = Opaque (get_name smb) %% [] in
  let op = assign op smb_prop smb in
  op


(* {3 Main} *)

(* TODO Implement typelvl=1 *)

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

    else if has oe Props.bproj_prop then
      let ty0 = get oe Props.bproj_prop in
      let oe = self#expr scx (remove oe Props.bproj_prop) in
      let smb = mk_smb (True ty0) in
      let opq = mk_opq smb in
      let op = assign (Internal B.Eq %% []) Props.tpars_prop [ ty0 ] in
      Apply (op, [ oe ; opq ]) %% []
    else

    begin match oe.core with

    (* FIXME a bit dirty *)
    | Apply ({ core = Opaque "IsAFcn" } as op, [ e ]) ->
        let e = self#expr scx e in
        let smb = mk_smb FunIsafcn in
        let opq = mk_opq smb $$ op in
        Apply (opq, [ e ]) @@ oe

    | Opaque s ->
        let ty2 = Ty2 ([], TAtm TAIdv) in
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

          | STRING,     Some [ ]              -> TStrSet
          | Int,        Some [ ]              -> TIntSet
          | Nat,        Some [ ]              -> TNatSet
          | Plus,       Some [ TAtm TAInt ]   -> TIntPlus
          | Uminus,     Some [ TAtm TAInt ]   -> TIntUminus
          | Minus,      Some [ TAtm TAInt ]   -> TIntMinus
          | Times,      Some [ TAtm TAInt ]   -> TIntTimes
          | Exp,        Some [ TAtm TAInt ]   -> TIntExp
          | Quotient,   Some [ ]              -> TIntQuotient
          | Remainder,  Some [ ]              -> TIntRemainder
          | Lteq,       Some [ TAtm TAInt ]   -> TIntLteq
          | Lt,         Some [ TAtm TAInt ]   -> TIntLt
          | Gteq,       Some [ TAtm TAInt ]   -> TIntGteq
          | Gt,         Some [ TAtm TAInt ]   -> TIntGt
          | Range,      Some [ ]              -> TIntRange

          | (Plus | Uminus | Minus | Times | Exp | Lteq | Lt | Gteq | Gt),
                        Some [ TAtm TARel ]   ->
              error ~at:oe "Real numbers not implemented"
          | _,          Some _      ->
              error ~at:oe "T1 not implemented"
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
          error ~at:oe "T1 not implemented"
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
          error ~at:oe "T1 not implemented"
        else
          let smb = mk_smb SetSt in
          let opq = mk_opq smb in
          Apply (opq, [ e1 ; Lambda ([ v, Shape_expr ], e2) %% [] ]) %% []

    | SetOf (e, bs) ->
        let scx, bs = self#bounds scx bs in
        let e = self#expr scx e in
        if has oe Props.tpars_prop then
          error ~at:oe "T1 not implemented"
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
        if has oe Props.tpars_prop then
          let smb = mk_smb (TStrLit str) in
          let opq = mk_opq smb in
          opq
        else
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
          error ~at:oe "T1 not implemented"
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
          error ~at:oe "T1 not implemented"
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
          error ~at:oe "T1 not implemented"
        else
          let smb = mk_smb FunApp in
          let opq = mk_opq smb in
          Apply (opq, [ e1 ; e2 ]) %% []

    | Except (e1, [ [ Except_apply e2 ], e3 ]) ->
        let e1 = self#expr scx e1 in
        let e2 = self#expr scx e2 in
        let e3 = self#expr scx e3 in
        if has oe Props.tpars_prop then
          error ~at:oe "T1 not implemented"
        else
          let smb = mk_smb FunExcept in
          let opq = mk_opq smb in
          Apply (opq, [ e1 ; e2 ; e3 ]) %% []
    | Except (e1, [ [ Except_dot s ], e3 ]) ->
        let e1 = self#expr scx e1 in
        let e3 = self#expr scx e3 in
        if has oe Props.tpars_prop then
          error ~at:oe "T1 not implemented"
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
          error ~at:oe "T1 not implemented"
        else
          let n = List.length es in
          let smb = mk_smb (Tuple n) in
          let opq = mk_opq smb in
          Apply (opq, es) %% []

    | Product es ->
        let es = List.map (self#expr scx) es in
        if has oe Props.tpars_prop then
          error ~at:oe "T1 not implemented"
        else
          let n = List.length es in
          let smb = mk_smb (Product n) in
          let opq = mk_opq smb in
          Apply (opq, es) %% []

    | Record fs ->
        let fs = List.map (fun (f, e) -> (f, self#expr scx e)) fs in
        if has oe Props.tpars_prop then
          error ~at:oe "T1 not implemented"
        else
          let fs, es = List.split fs in
          let smb = mk_smb (Rec fs) in
          let opq = mk_opq smb in
          Apply (opq, es) %% []

    | Rect fs ->
        let fs = List.map (fun (f, e) -> (f, self#expr scx e)) fs in
        if has oe Props.tpars_prop then
          error ~at:oe "T1 not implemented"
        else
          let fs, es = List.split fs in
          let smb = mk_smb (RecSet fs) in
          let opq = mk_opq smb in
          Apply (opq, es) %% []

    | Dot (e, s) ->
        let e = self#expr scx e in
        if has oe Props.tpars_prop then
          error ~at:oe "T1 not implemented"
        else
          let smb = mk_smb FunApp in
          let opq = mk_opq smb in
          let strlit = mk_smb (StrLit s) in
          let strlit_opq = mk_opq strlit in
          Apply (opq, [ e ; strlit_opq ]) %% []

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


let main sq =
  let cx = ((), Deque.empty) in
  let _, sq = visitor#sequent cx sq in
  sq

