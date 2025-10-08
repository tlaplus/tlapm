open Util

(** Propose proof decomposition CodeAction for an assumption in the form of
    disjunction.
    - The proof is split to multiple steps "by cases", in the same level as the
      QED step for which the action is proposed.
    - The decomposition is only proposed if the current context don't have one
      of the disjuncts among the assumptions. This way we don't repeat proposing
      the same. *)
let cas_of_assm_disj (uri : LspT.DocumentUri.t) (ps : PS.t) (ps_parent : PS.t)
    cx disjuncts =
  (* TODO: Stop proposing the disjunction... *)
  (* TODO: Name code actions by the nearest definition? *)
  let step_names = Seq_acc.make (PS.sub_step_name_seq ps_parent) in
  let ps_proof = PS.proof ps |> Option.get in
  let add_steps_rewrite =
    flatten_op_list Disj disjuncts
    |> List.map (fun disj ->
           let step_no = Seq_acc.take step_names in
           let step = TL.Proof.T.Pcase (disj, ps_proof) |> noprops in
           (step_no, step))
    |> pp_proof_steps_before ps cx
  in
  let ps_proof_rewrite =
    ps_proof_rewrite ps cx
      (`Usable
         Usable.(
           empty
           |> add_steps (Seq_acc.acc step_names)
           |> add_defs_from_pf ps_proof))
  in
  let ca =
    ca_edits ~uri ~title:"⤮ Decompose given (\\/)"
      ~edits:[ add_steps_rewrite; ps_proof_rewrite ]
  in
  [ ca ]

(** Match an assumption expression by its structure and propose the LSP Code
    actions to decompose them. *)
let cas_of_assm (uri : LspT.DocumentUri.t) (ps : PS.t) (ps_parent : PS.t) cx ex
    =
  let rec match_expr cx (ex : TL.Expr.T.expr) =
    match ex.core with
    | TL.Expr.T.Apply (op, op_args) -> (
        match op.core with
        | TL.Expr.T.Internal bi -> (
            match bi with
            | TL.Builtin.Disj -> cas_of_assm_disj uri ps ps_parent cx op_args
            | TL.Builtin.Implies | TL.Builtin.Conj | TL.Builtin.Equiv
            | TL.Builtin.TRUE | TL.Builtin.FALSE | TL.Builtin.Neg
            | TL.Builtin.Eq | TL.Builtin.Neq | TL.Builtin.STRING
            | TL.Builtin.BOOLEAN | TL.Builtin.SUBSET | TL.Builtin.UNION
            | TL.Builtin.DOMAIN | TL.Builtin.Subseteq | TL.Builtin.Mem
            | TL.Builtin.Notmem | TL.Builtin.Setminus | TL.Builtin.Cap
            | TL.Builtin.Cup | TL.Builtin.Prime | TL.Builtin.StrongPrime
            | TL.Builtin.Leadsto | TL.Builtin.ENABLED | TL.Builtin.UNCHANGED
            | TL.Builtin.Cdot | TL.Builtin.Actplus | TL.Builtin.Box _
            | TL.Builtin.Diamond | TL.Builtin.Nat | TL.Builtin.Int
            | TL.Builtin.Real | TL.Builtin.Plus | TL.Builtin.Minus
            | TL.Builtin.Uminus | TL.Builtin.Times | TL.Builtin.Ratio
            | TL.Builtin.Quotient | TL.Builtin.Remainder | TL.Builtin.Exp
            | TL.Builtin.Infinity | TL.Builtin.Lteq | TL.Builtin.Lt
            | TL.Builtin.Gteq | TL.Builtin.Gt | TL.Builtin.Divides
            | TL.Builtin.Range | TL.Builtin.Seq | TL.Builtin.Len
            | TL.Builtin.BSeq | TL.Builtin.Cat | TL.Builtin.Append
            | TL.Builtin.Head | TL.Builtin.Tail | TL.Builtin.SubSeq
            | TL.Builtin.SelectSeq | TL.Builtin.OneArg | TL.Builtin.Extend
            | TL.Builtin.Print | TL.Builtin.PrintT | TL.Builtin.Assert
            | TL.Builtin.JavaTime | TL.Builtin.TLCGet | TL.Builtin.TLCSet
            | TL.Builtin.Permutations | TL.Builtin.SortSeq
            | TL.Builtin.RandomElement | TL.Builtin.Any | TL.Builtin.ToString
            | TL.Builtin.Unprimable | TL.Builtin.Irregular ->
                [])
        | _ -> [])
    | TL.Expr.T.Quant (_, _, _) | TL.Expr.T.List (_, _) -> []
    | TL.Expr.T.Ix ix -> expand_expr_ref cx ix match_expr
    | TL.Expr.T.Opaque _ | TL.Expr.T.Internal _
    | TL.Expr.T.Lambda (_, _)
    | TL.Expr.T.Sequent _
    | TL.Expr.T.Bang (_, _)
    | TL.Expr.T.With (_, _)
    | TL.Expr.T.If (_, _, _)
    | TL.Expr.T.Let (_, _)
    | TL.Expr.T.QuantTuply (_, _, _)
    | TL.Expr.T.Tquant (_, _, _)
    | TL.Expr.T.Choose (_, _, _)
    | TL.Expr.T.ChooseTuply (_, _, _)
    | TL.Expr.T.SetSt (_, _, _)
    | TL.Expr.T.SetStTuply (_, _, _)
    | TL.Expr.T.SetOf (_, _)
    | TL.Expr.T.SetOfTuply (_, _)
    | TL.Expr.T.SetEnum _ | TL.Expr.T.Product _ | TL.Expr.T.Tuple _
    | TL.Expr.T.Fcn (_, _)
    | TL.Expr.T.FcnTuply (_, _)
    | TL.Expr.T.FcnApp (_, _)
    | TL.Expr.T.Arrow (_, _)
    | TL.Expr.T.Rect _ | TL.Expr.T.Record _
    | TL.Expr.T.Except (_, _)
    | TL.Expr.T.Dot (_, _)
    | TL.Expr.T.Sub (_, _, _)
    | TL.Expr.T.Tsub (_, _, _)
    | TL.Expr.T.Fair (_, _, _)
    | TL.Expr.T.Case (_, _)
    | TL.Expr.T.String _
    | TL.Expr.T.Num (_, _)
    | TL.Expr.T.At _
    | TL.Expr.T.Parens (_, _) ->
        []
  in
  match_expr cx ex

let code_actions (uri : LspT.DocumentUri.t) (ps : PS.t) (ps_parent : PS.t)
    (cx : TL.Expr.T.ctx) =
  let acc = ref [] in
  let append add = acc := List.append !acc add in
  let rec traverse_cx cx =
    match TL.Util.Deque.rear cx with
    | None -> ()
    | Some (cx, hyp) ->
        (match hyp |> unwrap with
        | TL.Expr.T.Fresh (_, _, _, _)
        | TL.Expr.T.FreshTuply (_, _)
        | TL.Expr.T.Flex _
        | TL.Expr.T.Defn (_, _, _, _)
        | TL.Expr.T.Fact (_, TL.Expr.T.Hidden, _) ->
            ()
        | TL.Expr.T.Fact (ex, TL.Expr.T.Visible, _) ->
            append (cas_of_assm uri ps ps_parent cx ex));
        traverse_cx cx
  in
  traverse_cx cx;
  !acc
