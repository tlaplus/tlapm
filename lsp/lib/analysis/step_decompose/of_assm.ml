open Util

(** Transform context so that all the hypotheses become hidden. That's to make
    printed expression as small/compact as possible. *)
let make_cx_hidden (cx : TL.Expr.T.ctx) : TL.Expr.T.ctx =
  let open TL.Expr.T in
  cx
  |> TL.Util.Deque.map @@ fun _ hyp ->
     match unwrap hyp with
     | Fresh (_, _, _, _) | FreshTuply (_, _) | Flex _ -> hyp
     | Defn (defn, wheredef, _, export) ->
         TL.Property.( @@ ) (Defn (defn, wheredef, Hidden, export)) hyp
     | Fact (expr, _, time) ->
         TL.Property.( @@ ) (Fact (expr, Hidden, time)) hyp

(** Limit length of a title, when referring to expressions. *)
let limit_title title =
  let max_len = 50 in
  if String.length title > max_len then String.sub title 0 (max_len - 1) ^ "…"
  else title

(** Propose the decomposition Code Action for an assumption which is in the form
    of conjunction. If we have an assumption
    {v
      A /\ B /\ ...
    v}
    with the current proof [pf], we will add steps before the QED step:
    {v
      <1>a. A [pf]
      <1>b. B [pf]
      ...
    v} *)
let cas_of_assm_conj (uri : LspT.DocumentUri.t) (ps : PS.t) (ps_parent : PS.t)
    cx conjuncts =
  (* TODO: Stop proposing the conjunction... *)
  (* TODO: Name code actions by the nearest definition? *)
  let step_names = Seq_acc.make (PS.stepno_seq_under_proof_step ps_parent) in
  let ps_proof = PS.proof ps |> Option.get in
  let conjuncts = flatten_op_list Conj conjuncts in
  let add_steps_rewrite =
    conjuncts
    |> List.map (fun conj ->
           let step_no = Seq_acc.take step_names in
           let step =
             TL.Proof.T.Assert (Sequent.of_goal conj, ps_proof) |> noprops
           in
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
  let title_ex = make_conjunction conjuncts in
  let title =
    Fmt.str "⤮ Split %a" (Debug.pp_expr_text (make_cx_hidden cx)) title_ex
    |> limit_title
  in
  let ca =
    ca_edits ~uri ~title ~edits:[ add_steps_rewrite; ps_proof_rewrite ]
  in
  [ ca ]

(** Propose proof decomposition Code Action for an assumption in the form of
    disjunction.
    - The proof is split to multiple steps "by cases", in the same level as the
      QED step for which the action is proposed.
    - The decomposition is only proposed if the current context don't have one
      of the disjuncts among the assumptions. This way we don't repeat proposing
      the same.

    Thus, if we have an assumption
    {v
      A \/ B \/ ...
    v}
    with the current proof [pf], we will add steps before the QED step:
    {v
      <1>a. CASE A [pf + <1>a]
      <1>b. CASE B [pf + <1>b]
      ...
      <1> QED [<1>a, <1>b, ... + defs from pf]
    v} *)
let cas_of_assm_disj (uri : LspT.DocumentUri.t) (ps : PS.t) (ps_parent : PS.t)
    cx disjuncts =
  (* TODO: Stop proposing the disjunction... *)
  (* TODO: Name code actions by the nearest definition? *)
  let step_names = Seq_acc.make (PS.stepno_seq_under_proof_step ps_parent) in
  let ps_proof = PS.proof ps |> Option.get in
  let disjuncts = flatten_op_list Disj disjuncts in
  let add_steps_rewrite =
    disjuncts
    |> List.map (fun disj ->
           let step_no = Seq_acc.take step_names in
           let step_pf =
             Usable.(empty |> add_steps [ step_no ] |> add_to_pf ps_proof)
           in
           let step = TL.Proof.T.Pcase (disj, step_pf) |> noprops in
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
  let title_ex = make_disjunction disjuncts in
  let title =
    Fmt.str "⤮ Case split %a" (Debug.pp_expr_text (make_cx_hidden cx)) title_ex
    |> limit_title
  in
  let ca =
    ca_edits ~uri ~title ~edits:[ add_steps_rewrite; ps_proof_rewrite ]
  in
  [ ca ]

(** Propose use of an assumption in the form of an implication. Thus, if we have
    assumption
    {v
      A => B => ... => C
    v}
    with the current proof [pf] we will produce
    {v
      <1>a. C
        <2>a. A [pf]
        <2>b. B [pf]
        ...
        <2> QED [<2>a, <2>b, ... + pf]
      <1> QED [<1>a + pf]
    v} *)
let cas_of_assm_implies (uri : LspT.DocumentUri.t) (ps : PS.t)
    (ps_parent : PS.t) cx args =
  Fmt.epr "XXX: cas_of_assm_implies, args=%a@."
    (Fmt.list ~sep:Fmt.(const string ", ") (Debug.pp_expr_text cx))
    args;
  let antecedents, consequent =
    match args |> flatten_op_list Implies |> List.rev with
    | c :: a -> (List.rev a, c)
    | [] -> assert false
  in
  Fmt.epr "XXX: cas_of_assm_implies, antecedents=%a@."
    (Fmt.list ~sep:Fmt.(const string ", ") (Debug.pp_expr_text cx))
    antecedents;
  Fmt.epr "XXX: cas_of_assm_implies, consequent=%a@." (Debug.pp_expr_text cx)
    consequent;
  let step_names = Seq_acc.make (PS.stepno_seq_under_proof_step ps_parent) in
  let ps_proof = PS.proof ps |> Option.get in
  let add_steps_rewrite =
    let step_no = Seq_acc.take step_names in
    let step_pf =
      let sub_stepno_seq =
        PS.stepno_seq_under_stepno (Some step_no) |> Seq_acc.make
      in
      let sub_steps =
        antecedents
        |> List.mapi @@ fun i antecedent ->
           let antecedent =
             (* On the shift and cx. My [KP] guess follows:
               - Each assert takes 1 bump (1 for main step, and 1 for each sub-step)
               - Each named step does a bump for a name (of a step).
               - The current step has the name, but not the assert yet, thus +1.
             *)
             antecedent |> TL.Expr.Subst.(app_expr (shift (2 + (i * 2) + 1)))
           in
           let sub_step_no = Seq_acc.take sub_stepno_seq in
           let sub_step =
             TL.Proof.T.(Assert (Sequent.of_goal antecedent, ps_proof))
             |> noprops
           in
           TL.Property.assign sub_step TL.Proof.T.Props.step sub_step_no
      in
      let step_qed_pf =
        Usable.(
          empty |> add_steps (Seq_acc.acc sub_stepno_seq) |> add_to_pf ps_proof)
      in
      let step_qed_sn = Seq_acc.take sub_stepno_seq in
      let step_qed = TL.Proof.T.Qed step_qed_pf |> noprops in
      let step_qed =
        TL.Property.assign step_qed TL.Proof.T.Props.step step_qed_sn
      in
      TL.Proof.T.Steps (sub_steps, step_qed) |> noprops
    in
    let step =
      TL.Proof.T.(Assert (Sequent.of_goal consequent, step_pf)) |> noprops
    in
    [ (step_no, step) ] |> pp_proof_steps_before ps cx
  in
  let ps_proof_rewrite =
    ps_proof_rewrite ps cx
      (`Proof
         Usable.(
           empty |> add_steps (Seq_acc.acc step_names) |> add_to_pf ps_proof))
  in
  let title_ex =
    TL.Expr.T.(Apply (Internal TL.Builtin.Implies |> noprops, args)) |> noprops
  in
  let title =
    Fmt.str "⤮ Use %a" (Debug.pp_expr_text (make_cx_hidden cx)) title_ex
    |> limit_title
  in
  let ca =
    ca_edits ~uri ~title ~edits:[ add_steps_rewrite; ps_proof_rewrite ]
  in
  [ ca ]

(** Match an assumption expression by its structure and propose the LSP Code
    actions to decompose them. *)
let cas_of_assm (uri : LspT.DocumentUri.t) (ps : PS.t) (ps_parent : PS.t) cx ex
    =
  Fmt.epr "XXX: assm=%a@." Debug.pp_expr ex;
  let rec match_expr cx (ex : TL.Expr.T.expr) =
    match ex.core with
    | TL.Expr.T.Apply (op, op_args) -> (
        match op.core with
        | TL.Expr.T.Internal bi -> (
            match bi with
            | TL.Builtin.Conj -> cas_of_assm_conj uri ps ps_parent cx op_args
            | TL.Builtin.Disj -> cas_of_assm_disj uri ps ps_parent cx op_args
            | TL.Builtin.Implies ->
                cas_of_assm_implies uri ps ps_parent cx op_args
            | TL.Builtin.Equiv | TL.Builtin.TRUE | TL.Builtin.FALSE
            | TL.Builtin.Neg | TL.Builtin.Eq | TL.Builtin.Neq
            | TL.Builtin.STRING | TL.Builtin.BOOLEAN | TL.Builtin.SUBSET
            | TL.Builtin.UNION | TL.Builtin.DOMAIN | TL.Builtin.Subseteq
            | TL.Builtin.Mem | TL.Builtin.Notmem | TL.Builtin.Setminus
            | TL.Builtin.Cap | TL.Builtin.Cup | TL.Builtin.Prime
            | TL.Builtin.StrongPrime | TL.Builtin.Leadsto | TL.Builtin.ENABLED
            | TL.Builtin.UNCHANGED | TL.Builtin.Cdot | TL.Builtin.Actplus
            | TL.Builtin.Box _ | TL.Builtin.Diamond | TL.Builtin.Nat
            | TL.Builtin.Int | TL.Builtin.Real | TL.Builtin.Plus
            | TL.Builtin.Minus | TL.Builtin.Uminus | TL.Builtin.Times
            | TL.Builtin.Ratio | TL.Builtin.Quotient | TL.Builtin.Remainder
            | TL.Builtin.Exp | TL.Builtin.Infinity | TL.Builtin.Lteq
            | TL.Builtin.Lt | TL.Builtin.Gteq | TL.Builtin.Gt
            | TL.Builtin.Divides | TL.Builtin.Range | TL.Builtin.Seq
            | TL.Builtin.Len | TL.Builtin.BSeq | TL.Builtin.Cat
            | TL.Builtin.Append | TL.Builtin.Head | TL.Builtin.Tail
            | TL.Builtin.SubSeq | TL.Builtin.SelectSeq | TL.Builtin.OneArg
            | TL.Builtin.Extend | TL.Builtin.Print | TL.Builtin.PrintT
            | TL.Builtin.Assert | TL.Builtin.JavaTime | TL.Builtin.TLCGet
            | TL.Builtin.TLCSet | TL.Builtin.Permutations | TL.Builtin.SortSeq
            | TL.Builtin.RandomElement | TL.Builtin.Any | TL.Builtin.ToString
            | TL.Builtin.Unprimable | TL.Builtin.Irregular ->
                [])
        | _ -> [])
    | TL.Expr.T.List (bullet, exprs) -> (
        match bullet with
        | TL.Expr.T.And | TL.Expr.T.Refs ->
            cas_of_assm_conj uri ps ps_parent cx exprs
        | TL.Expr.T.Or -> cas_of_assm_disj uri ps ps_parent cx exprs)
    | TL.Expr.T.Sub (modal_op, action_ex, subscript_ex) ->
        expand_sub modal_op action_ex subscript_ex |> match_expr cx
    | TL.Expr.T.Ix ix -> expand_expr_ref cx ix match_expr
    | TL.Expr.T.Quant (_, _, _)
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
        Fmt.epr "XXX: hyp=%a@." Debug.pp_hyp hyp;
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
