open Util

(* Create code action for a goal in the form of implication. *)
let cas_of_goal_implies (uri : LspT.DocumentUri.t) (ps : PS.t)
    (ps_parent : PS.t) (cx : TL.Expr.T.ctx) (op_args : TL.Expr.T.expr list) =
  let ps_proof = PS.proof ps |> Option.get in
  let step_names = Seq_acc.make (PS.stepno_seq_under_proof_step ps_parent) in
  let antecedent = List.hd op_args in
  let step = TL.Proof.T.Have antecedent |> noprops in
  let step_no = Seq_acc.take step_names in
  let title = "⤮ Decompose goal (=>)" in
  let add_steps_rewrite = [ (step_no, step) ] |> pp_proof_steps_before ps cx in
  let ps_proof_rewrite =
    ps_proof_rewrite ps cx
      (`Usable
         Usable.(
           empty
           |> add_steps (Seq_acc.acc step_names)
           |> add_defs_from_pf ps_proof))
  in
  let ca =
    ca_edits ~uri ~title ~edits:[ add_steps_rewrite; ps_proof_rewrite ]
  in
  [ ca ]

(** Create code action for a goal in the form of universal quantification. *)
let cas_of_goal_forall (uri : LspT.DocumentUri.t) (ps : PS.t) (ps_parent : PS.t)
    (cx : TL.Expr.T.ctx) (bs : TL.Expr.T.bound list) =
  let title = "⤮ Decompose goal (\\A)" in
  let step = TL.Proof.T.Take bs |> noprops in
  let edit =
    [ (PS.sub_step_unnamed ps_parent, step) ] |> pp_proof_steps_before ps cx
  in
  let ca = ca_edits ~uri ~title ~edits:[ edit ] in
  [ ca ]

(** Create code action for a goal in the form of existential quantification.

    {v
      THEOREM TestGoalExists ==
        ASSUME NEW P(_, _), NEW S
        PROVE \E a, b \in S : P(a, b)
      PROOF
        \* <1> USE OBVIOUS
        <1> DEFINE a == TRUE
        <1> DEFINE b == TRUE
        <1> HIDE DEF a, b
        <1>1. a \in S
        <1>2. b \in S
        <1> WITNESS a \in S, b \in S
        <1>3. QED OBVIOUS
    v}

    - For each bound, define a constant.
    - Hide all defined constants.
    - For each bound with a domain, introduce domain proof step.
    - Then introduce the witness step. *)
let cas_of_goal_exists (uri : LspT.DocumentUri.t) (ps : PS.t) (ps_parent : PS.t)
    (cx : TL.Expr.T.ctx) (bs : TL.Expr.T.bound list) =
  let title = "⤮ Decompose goal (\\E)" in
  let step_names = Seq_acc.make (PS.stepno_seq_under_proof_step ps_parent) in
  let bs_unditto = TL.Expr.T.unditto bs in
  let fcx = fmt_cx cx in
  let fresh_names = ref [] in
  let steps_def =
    bs
    |> List.map @@ fun (b_name, _, _) ->
       let fresh_var_name = fresh_ident fcx (unwrap b_name) in
       fresh_names := fresh_var_name :: !fresh_names;
       let step_no = PS.sub_step_unnamed ps_parent in
       let step =
         TL.Proof.T.Define
           [
             TL.Expr.T.Operator
               ( b_name,
                 TL.Expr.T.String
                   (Fmt.str "TODO: Replace this with actual witness for %s"
                      fresh_var_name)
                 |> noprops )
             |> noprops;
           ]
         |> noprops
       in
       (step_no, step)
  in
  let fresh_names = List.rev !fresh_names in
  let step_hide =
    let defs =
      fresh_names |> List.map @@ fun name -> TL.Proof.T.Dvar name |> noprops
    in
    let step_no = PS.sub_step_unnamed ps_parent in
    let step = TL.Proof.T.Hide { facts = []; defs } |> noprops in
    (step_no, step)
  in
  let steps_pf_dom =
    bs_unditto
    |> ( List.mapi @@ fun pos (_, _, b_dom) ->
         let fresh_name = List.nth fresh_names pos in
         match b_dom with
         | TL.Expr.T.Domain dom_expr ->
             let active =
               TL.Expr.T.Apply
                 ( TL.Expr.T.Internal TL.Builtin.Mem |> noprops,
                   [ TL.Expr.T.Opaque fresh_name |> noprops; dom_expr ] )
               |> noprops
             in
             let step =
               TL.Proof.T.Assert
                 ( Sequent.of_goal active,
                   TL.Proof.T.(Omitted Implicit) |> noprops )
               |> noprops
             in
             let step_no = Seq_acc.take step_names in
             Some (step_no, step)
         | TL.Expr.T.No_domain | TL.Expr.T.Ditto -> None )
    |> List.filter_map (fun x -> x)
  in
  let step_use =
    Option.bind (PS.proof ps) @@ fun pf ->
    match pf.core with
    | TL.Proof.T.By (usable, only) ->
        let step_no = Seq_acc.take step_names in
        let step = TL.Proof.T.Use (usable, only) |> noprops in
        Some (step_no, step)
    | TL.Proof.T.Obvious | TL.Proof.T.Omitted _
    | TL.Proof.T.Steps (_, _)
    | TL.Proof.T.Error _ ->
        None
  in
  let step_witness =
    let exprs =
      bs_unditto
      |> List.mapi @@ fun pos (_, _, b_dom) ->
         let fresh_name = List.nth fresh_names pos in
         match b_dom with
         | TL.Expr.T.No_domain | TL.Expr.T.Ditto ->
             TL.Expr.T.Opaque fresh_name |> noprops
         | TL.Expr.T.Domain dom ->
             TL.Expr.T.Apply
               ( TL.Expr.T.Internal TL.Builtin.Mem |> noprops,
                 [ TL.Expr.T.Opaque fresh_name |> noprops; dom ] )
             |> noprops
    in
    let step = TL.Proof.T.Witness exprs |> noprops in
    let step_no = PS.sub_step_unnamed ps_parent in
    (step_no, step)
  in
  let edit =
    List.concat
      [
        steps_def;
        [ step_hide ];
        steps_pf_dom;
        Option.to_list step_use;
        [ step_witness ];
      ]
    |> pp_proof_steps_before ps cx
  in
  let ca = ca_edits ~uri ~title ~edits:[ edit ] in
  [ ca ]

(** Create a code action for a goal in the form of conjunction. *)
let cas_of_goal_conj (uri : LspT.DocumentUri.t) (ps : PS.t) (ps_parent : PS.t)
    cx op_args =
  let step_names = Seq_acc.make (PS.stepno_seq_under_proof_step ps_parent) in
  let ps_proof = PS.proof ps |> Option.get in
  let add_steps_rewrite =
    flatten_op_list Conj op_args
    |> List.map (fun op ->
           let step_no = Seq_acc.take step_names in
           let step =
             TL.Proof.T.Assert (Sequent.of_goal op, ps_proof) |> noprops
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
  let ca =
    ca_edits ~uri ~title:"⤮ Decompose goal (/\\)"
      ~edits:[ add_steps_rewrite; ps_proof_rewrite ]
  in
  [ ca ]

(** Make decomposition code actions for a goal of the form of disjunction. In
    general we leave one disjunct as a goal and assume all the rest are negated.
    - We don't know which one to pick, thus propose user all of them.
    - The current step proof is then replaced with the BY <x>y referring to the
      introduced SUFFICES. *)
let cas_of_goal_disj (uri : LspT.DocumentUri.t) (ps : PS.t) (ps_parent : PS.t)
    cx disjuncts =
  let disjuncts = flatten_op_list Disj disjuncts in
  let ps_proof = PS.proof ps |> Option.get in
  let disjunct_ca disjunct_pos disjunct =
    let step_names = Seq_acc.make (PS.stepno_seq_under_proof_step ps_parent) in
    let step_no = Seq_acc.take step_names in
    let other_negated =
      disjuncts
      |> List.filteri (fun i _ -> i != disjunct_pos)
      |> List.mapi (fun i disjunct ->
             (* TODO: Drop existing negation, if there exist instead of adding yet another. *)
             let expr =
               TL.Expr.T.Apply
                 (TL.(Expr.T.Internal Builtin.Neg) |> noprops, [ disjunct ])
               |> noprops
             in
             TL.Expr.T.(Fact (expr, Visible, NotSet))
             |> noprops
             |> TL.Expr.Subst.(app_hyp (shift i)))
    in
    let disjunct =
      disjunct |> TL.Expr.Subst.(app_expr (shift (List.length other_negated)))
    in
    let step =
      TL.Proof.T.Suffices
        ( { context = TL.Util.Deque.of_list other_negated; active = disjunct },
          ps_proof )
      |> noprops
    in
    let new_step_rewrite = pp_proof_steps_before ps cx [ (step_no, step) ] in
    let ps_proof_rewrite = ps_proof_rewrite ps cx (`StepNames [ step_no ]) in
    ca_edits ~uri
      ~title:(Fmt.str "⤮ Decompose goal (\\/, case %d)" (disjunct_pos + 1))
      ~edits:[ new_step_rewrite; ps_proof_rewrite ]
  in
  List.mapi disjunct_ca disjuncts

(* A chain of equivalences is replaced with a list of circular implications. *)
let cas_of_goal_equiv (uri : LspT.DocumentUri.t) (ps : PS.t) (ps_parent : PS.t)
    cx op_args =
  let step_names = Seq_acc.make (PS.stepno_seq_under_proof_step ps_parent) in
  let add_steps_rewrite =
    let ps_proof = PS.proof ps |> Option.get in
    let op_args = flatten_op_list Equiv op_args in
    let next_arg i = List.nth op_args ((i + 1) mod List.length op_args) in
    op_args
    |> List.mapi (fun i op ->
           let step_no = Seq_acc.take step_names in
           let step_goal =
             TL.Expr.T.Apply
               ( TL.Expr.T.Internal TL.Builtin.Implies |> noprops,
                 [ op; next_arg i ] )
             |> noprops
           in
           let step =
             TL.Proof.T.Assert (Sequent.of_goal step_goal, ps_proof) |> noprops
           in
           (step_no, step))
    |> pp_proof_steps_before ps cx
  in
  let ps_proof_rewrite =
    ps_proof_rewrite ps cx (`StepNames (Seq_acc.acc step_names))
  in
  let ca =
    ca_edits ~uri ~title:"⤮ Decompose goal (<=>)"
      ~edits:[ add_steps_rewrite; ps_proof_rewrite ]
  in
  [ ca ]

let code_actions (uri : LspT.DocumentUri.t) (ps : PS.t) (ps_parent : PS.t)
    (sq : TL.Expr.T.sequent) =
  let rec match_expr cx (ex : TL.Expr.T.expr) =
    (* Fmt.epr "@[match_goal@, ex=%a@, cx=%a@]@." (Debug.pp_expr_text cx) ex
      Debug.pp_cx cx; *)
    match ex.core with
    | TL.Expr.T.Apply (op, op_args) -> (
        match op.core with
        | TL.Expr.T.Internal bi -> (
            match bi with
            | TL.Builtin.Implies ->
                cas_of_goal_implies uri ps ps_parent cx op_args
            | TL.Builtin.Conj -> cas_of_goal_conj uri ps ps_parent cx op_args
            | TL.Builtin.Disj -> cas_of_goal_disj uri ps ps_parent cx op_args
            | TL.Builtin.Equiv -> cas_of_goal_equiv uri ps ps_parent cx op_args
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
    | TL.Expr.T.Quant (q, bs, _e) -> (
        match q with
        | TL.Expr.T.Forall -> cas_of_goal_forall uri ps ps_parent cx bs
        | TL.Expr.T.Exists -> cas_of_goal_exists uri ps ps_parent cx bs)
    | TL.Expr.T.List (bullet, exprs) -> (
        match bullet with
        | TL.Expr.T.And | TL.Expr.T.Refs ->
            cas_of_goal_conj uri ps ps_parent cx exprs
        | TL.Expr.T.Or -> cas_of_goal_disj uri ps ps_parent cx exprs)
    | TL.Expr.T.Sub (modal_op, action_ex, subscript_ex) ->
        expand_sub modal_op action_ex subscript_ex |> match_expr cx
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
    | TL.Expr.T.Tsub (_, _, _)
    | TL.Expr.T.Fair (_, _, _)
    | TL.Expr.T.Case (_, _)
    | TL.Expr.T.String _
    | TL.Expr.T.Num (_, _)
    | TL.Expr.T.At _
    | TL.Expr.T.Parens (_, _) ->
        []
  in
  match_expr sq.context sq.active
