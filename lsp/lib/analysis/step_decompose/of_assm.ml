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
    Fmt.str "⤮ Split (∧): %a" (Debug.pp_expr_text (make_cx_hidden cx)) title_ex
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
      (`Proof
         Usable.(
           empty |> add_steps (Seq_acc.acc step_names) |> add_to_pf ps_proof))
  in
  let title_ex = make_disjunction disjuncts in
  let title =
    Fmt.str "⤮ Case split (∨): %a"
      (Debug.pp_expr_text (make_cx_hidden cx))
      title_ex
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
  let open TL in
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
             antecedent |> Expr.Subst.(app_expr (shift (2 + (i * 2) + 1)))
           in
           let sn = Seq_acc.take sub_stepno_seq in
           Proof.T.(Assert (Sequent.of_goal antecedent, ps_proof))
           |> noprops |> with_stepno sn
      in
      let step_qed =
        let pf =
          Usable.(
            empty
            |> add_steps (Seq_acc.acc sub_stepno_seq)
            |> add_to_pf ps_proof)
        in
        let sn = Seq_acc.take sub_stepno_seq in
        Proof.T.Qed pf |> noprops |> with_stepno sn
      in
      Proof.T.Steps (sub_steps, step_qed) |> noprops
    in
    let step =
      Proof.T.(Assert (Sequent.of_goal consequent, step_pf)) |> noprops
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
    Expr.T.(Apply (Internal Builtin.Implies |> noprops, args)) |> noprops
  in
  let title =
    Fmt.str "⤮ Use (⇒): %a" (Debug.pp_expr_text (make_cx_hidden cx)) title_ex
    |> limit_title
  in
  let ca =
    ca_edits ~uri ~title ~edits:[ add_steps_rewrite; ps_proof_rewrite ]
  in
  [ ca ]

(** For each assumption in the form of existential quantifier,
    {v
      \A x \in X : P(x)
    v}
    and [pf] as the current proof, we introduce
    {v
      <1>a. PICK x \in X : P(x)
        <2>1. X # {}
        <2>2. QED [pf + <2>1]
    v} *)
let cas_of_assm_forall (uri : LspT.DocumentUri.t) (ps : PS.t) (ps_parent : PS.t)
    cx bs ex =
  let open TL in
  let step_names = Seq_acc.make (PS.stepno_seq_under_proof_step ps_parent) in
  let ps_proof = PS.proof ps |> Option.get in
  let add_steps_rewrite =
    let step_no = Seq_acc.take step_names in
    let step_pf =
      let sub_stepno_seq =
        PS.stepno_seq_under_stepno (Some step_no) |> Seq_acc.make
      in
      let step_exists =
        let _, bs =
          (* See note in [cas_of_assm_implies]. *)
          bs |> Expr.Subst.(app_bounds (shift (2 + (0 * 2) + 1)))
        in
        let goal =
          Expr.T.(Quant (Exists, bs, Internal Builtin.TRUE |> noprops))
          |> noprops
        in
        let sn = Seq_acc.take sub_stepno_seq in
        Proof.T.Assert (Sequent.of_goal goal, ps_proof)
        |> noprops |> with_stepno sn
      in
      let step_qed =
        let pf =
          Usable.(
            empty
            |> add_steps (Seq_acc.acc sub_stepno_seq)
            |> add_to_pf ps_proof)
        in
        let sn = Seq_acc.take sub_stepno_seq in
        Proof.T.Qed pf |> noprops |> with_stepno sn
      in
      Proof.T.(Steps ([ step_exists ], step_qed)) |> noprops
    in
    let step = Proof.T.Pick (bs, ex, step_pf) |> noprops in
    [ (step_no, step) ] |> pp_proof_steps_before ps cx
  in
  let ps_proof_rewrite =
    ps_proof_rewrite ps cx
      (`Proof
         Usable.(
           empty |> add_steps (Seq_acc.acc step_names) |> add_to_pf ps_proof))
  in
  let title_ex = Expr.T.(Quant (Expr.T.Forall, bs, ex)) |> noprops in
  let title =
    Fmt.str "⤮ Use (∀): %a" (Debug.pp_expr_text (make_cx_hidden cx)) title_ex
    |> limit_title
  in
  let ca =
    ca_edits ~uri ~title ~edits:[ add_steps_rewrite; ps_proof_rewrite ]
  in
  [ ca ]

(** For each assumption in the form of existential quantifier,
    {v
      \E x \in X : P(x)
    v}
    and [pf] as the current proof, we introduce
    {v
      <1>a. PICK x \in X : P(x) [pf]
    v} *)
let cas_of_assm_exists (uri : LspT.DocumentUri.t) (ps : PS.t) (ps_parent : PS.t)
    cx bs ex =
  let open TL in
  let step_names = Seq_acc.make (PS.stepno_seq_under_proof_step ps_parent) in
  let ps_proof = PS.proof ps |> Option.get in
  let add_steps_rewrite =
    let step_no = Seq_acc.take step_names in
    let step = Proof.T.Pick (bs, ex, ps_proof) |> noprops in
    [ (step_no, step) ] |> pp_proof_steps_before ps cx
  in
  let ps_proof_rewrite =
    ps_proof_rewrite ps cx
      (`Proof
         Usable.(
           empty |> add_steps (Seq_acc.acc step_names) |> add_to_pf ps_proof))
  in
  let title_ex = Expr.T.(Quant (Expr.T.Exists, bs, ex)) |> noprops in
  let title =
    Fmt.str "⤮ Use (∃): %a" (Debug.pp_expr_text (make_cx_hidden cx)) title_ex
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
  let open TL in
  Fmt.epr "XXX: assm=%a@." Debug.pp_expr ex;
  let rec match_expr cx (ex : Expr.T.expr) =
    match ex.core with
    | Apply (op, op_args) -> (
        match op.core with
        | Internal bi -> (
            match bi with
            | Conj -> cas_of_assm_conj uri ps ps_parent cx op_args
            | Disj -> cas_of_assm_disj uri ps ps_parent cx op_args
            | Implies -> cas_of_assm_implies uri ps ps_parent cx op_args
            | Equiv | TRUE | FALSE | Neg | Eq | Neq | STRING | BOOLEAN | SUBSET
            | UNION | DOMAIN | Subseteq | Mem | Notmem | Setminus | Cap | Cup
            | Prime | StrongPrime | Leadsto | ENABLED | UNCHANGED | Cdot
            | Actplus | Box _ | Diamond | Nat | Int | Real | Plus | Minus
            | Uminus | Times | Ratio | Quotient | Remainder | Exp | Infinity
            | Lteq | Lt | Gteq | Gt | Divides | Range | Seq | Len | BSeq | Cat
            | Append | Head | Tail | SubSeq | SelectSeq | OneArg | Extend
            | Print | PrintT | Assert | JavaTime | TLCGet | TLCSet
            | Permutations | SortSeq | RandomElement | Any | ToString
            | Unprimable | Irregular ->
                [])
        | _ -> [])
    | Quant (q, bs, e) -> (
        match q with
        | Forall -> cas_of_assm_forall uri ps ps_parent cx bs e
        | Exists -> cas_of_assm_exists uri ps ps_parent cx bs e)
    | List (bullet, exprs) -> (
        match exprs with
        | [] -> []
        | [ expr ] -> match_expr cx expr
        | _ :: _ -> (
            match bullet with
            | And | Refs -> cas_of_assm_conj uri ps ps_parent cx exprs
            | Or -> cas_of_assm_disj uri ps ps_parent cx exprs))
    | Sub (modal_op, action_ex, subscript_ex) ->
        expand_sub modal_op action_ex subscript_ex |> match_expr cx
    | Ix ix -> expand_expr_ref cx ix match_expr
    | Opaque _ | Internal _
    | Lambda (_, _)
    | Sequent _
    | Bang (_, _)
    | With (_, _)
    | If (_, _, _)
    | Let (_, _)
    | QuantTuply (_, _, _)
    | Tquant (_, _, _)
    | Choose (_, _, _)
    | ChooseTuply (_, _, _)
    | SetSt (_, _, _)
    | SetStTuply (_, _, _)
    | SetOf (_, _)
    | SetOfTuply (_, _)
    | SetEnum _ | Product _ | Tuple _
    | Fcn (_, _)
    | FcnTuply (_, _)
    | FcnApp (_, _)
    | Arrow (_, _)
    | Rect _ | Record _
    | Except (_, _)
    | Dot (_, _)
    | Tsub (_, _, _)
    | Fair (_, _, _)
    | Case (_, _)
    | String _
    | Num (_, _)
    | At _
    | Parens (_, _) ->
        []
  in
  match_expr cx ex

let code_actions (uri : LspT.DocumentUri.t) (ps : PS.t) (ps_parent : PS.t)
    (cx : TL.Expr.T.ctx) =
  let open TL in
  let acc = ref [] in
  let append add = acc := List.append !acc add in
  let rec traverse_cx cx =
    match Util.Deque.rear cx with
    | None -> ()
    | Some (cx, hyp) ->
        Fmt.epr "XXX: hyp=%a@." Debug.pp_hyp hyp;
        (match hyp |> unwrap with
        | Fresh (_, _, _, _)
        | FreshTuply (_, _)
        | Flex _
        | Defn (_, _, _, _)
        | Fact (_, Hidden, _) ->
            ()
        | Fact (ex, Visible, _) -> append (cas_of_assm uri ps ps_parent cx ex));
        traverse_cx cx
  in
  traverse_cx cx;
  !acc
