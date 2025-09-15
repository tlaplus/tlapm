(* cspell:words Actplus Cdot Deque Disj Forall Gteq Leadsto Lteq Notmem Setminus Tquant Tquant Tsub Uminus Unprimable noprops stepno uncons *)
module PS = Docs.Proof_step
module TL = Tlapm_lib
module LspT = Lsp.Types

(* Collect recursively multiple nested operator applications. *)

type flatten_by = Conj | Disj | Equiv

let rec flatten_op_list (by : flatten_by) (exs : TL.Expr.T.expr list) :
    TL.Expr.T.expr list =
  exs |> List.map (fun arg -> flatten_op by arg) |> List.flatten

and flatten_op (by : flatten_by) (ex : TL.Expr.T.expr) : TL.Expr.T.expr list =
  match ex.core with
  | TL.Expr.T.Apply (op, args) -> (
      match op.core with
      | TL.Expr.T.Internal bi -> (
          match bi with
          | TL.Builtin.Conj when by = Conj -> flatten_op_list by args
          | TL.Builtin.Disj when by = Disj -> flatten_op_list by args
          | TL.Builtin.Equiv when by = Equiv -> flatten_op_list by args
          | _ -> [ ex ])
      | _ -> [ ex ])
  | TL.Expr.T.List (bullet, list) -> (
      match bullet with
      | TL.Expr.T.And when by = Conj -> flatten_op_list by list
      | TL.Expr.T.Or when by = Disj -> flatten_op_list by list
      | _ -> [ ex ])
  | _ -> [ ex ]

(* Helpers for formatting the TLA code. *)

(* TODO: A hacked-up approach to indentation. *)
let indent (ps : PS.t) ~nested text =
  let nested = if nested then 2 else 0 in
  let _line, char = PS.full_range ps |> Range.from |> Range.Position.as_pair in
  let indent =
    Array.make (char - 1 + nested) ' ' |> Array.to_seq |> String.of_seq
  in
  let template = String.cat "\n" indent in
  Re2.rewrite_exn (Re2.create_exn "\n") ~template text

let indent_size (ps : PS.t) ~nested =
  let nested = if nested then 2 else 0 in
  let _line, char = PS.full_range ps |> Range.from |> Range.Position.as_pair in
  char - 1 + nested

let fmt_cx cx = (cx, TL.Ctx.dot |> TL.Ctx.with_try_print_src)
let pp_proof cx fmt st = ignore (TL.Proof.Fmt.pp_print_proof (fmt_cx cx) fmt st)

let pp_proof_step cx fmt st =
  ignore (TL.Proof.Fmt.pp_print_step (fmt_cx cx) fmt st)

let pp_proof_step_no fmt (sn : TL.Proof.T.stepno) =
  let str = TL.Proof.T.string_of_stepno sn in
  match sn with
  | TL.Proof.T.Named (_, _, _) -> Fmt.pf fmt "%s." str
  | TL.Proof.T.Unnamed (_, _) -> Fmt.pf fmt "%s" str

let pp_proof_step_with_no cx fmt (step_no, step) =
  Fmt.pf fmt "@[%a @[%a@]@]" pp_proof_step_no step_no (pp_proof_step cx) step

let pp_proof_step_list ps cx steps =
  let indent = indent_size ps ~nested:false in
  Fmt.str "@[<v %d>%s%a@]@." indent (String.make indent ' ')
    (Fmt.list ~sep:Format.pp_force_newline (pp_proof_step_with_no cx))
    steps

let pp_proof_steps_before ps cx steps =
  let range = Range.make_before_ln (PS.full_range ps) in
  let text = pp_proof_step_list ps cx steps in
  (range, text)

(* let pp_proof_step_replace ps cx steps =
  (* TODO: Calculate the range properly. *)
  let range = Range.make_before_ln (PS.full_range ps) in
  let text = pp_proof_step_list ps cx steps in
  (range, text) *)

(* Helpers for constructing code actions. *)

let ca_edit ~uri ~title ~range ~newText =
  let edit = LspT.TextEdit.create ~newText ~range:(Range.as_lsp_range range) in
  let edit = LspT.WorkspaceEdit.create ~changes:[ (uri, [ edit ]) ] () in
  LspT.CodeAction.create ~title ~edit ()

let ca_edits ~uri ~title ~edits =
  let edits =
    List.map
      (fun (r, t) ->
        LspT.TextEdit.create ~newText:t ~range:(Range.as_lsp_range r))
      edits
  in
  let edit = LspT.WorkspaceEdit.create ~changes:[ (uri, edits) ] () in
  LspT.CodeAction.create ~title ~edit ()

(** Replace {v <1> ... v} with {v <1> ... OBVIOUS v} *)
let ca_omitted ~uri ~ps =
  let title = "Prove as OBVIOUS" in
  let range = PS.head_range ps |> Range.make_after in
  let newText = " OBVIOUS" in
  ca_edit ~uri ~title ~range ~newText

(** Replace
    {v
      <1> ...
        proof
    v}
    with
    {v
      <1> ...
        <2> QED proof
    v} *)
let ca_to_steps ~uri ~ps ~cx ~pf ~depth =
  let title = "Prove in steps." in
  let range =
    match TL.Util.query_locus pf with
    | Some _ ->
        Range.of_points
          (ps |> PS.head_range |> Range.make_after |> Range.from)
          (ps |> PS.full_range |> Range.till)
    | None -> PS.head_range ps |> Range.make_after
  in
  let qed_depth = depth + 1 in
  let pf_pp =
    TL.Proof.Fmt.pp_print_proof (cx, TL.Ctx.dot |> TL.Ctx.with_try_print_src)
  in
  let newText =
    indent ps ~nested:true (Fmt.str "\n<%d> QED %a" qed_depth pf_pp pf)
  in
  (* TODO: Use the PP for all the text... *)
  ca_edit ~uri ~title ~range ~newText

(* Propose code actions for AST nodes containing proofs. *)
let cas_of_el_with_pf (uri : LspT.DocumentUri.t) (ps : PS.t)
    (cx : TL.Expr.T.ctx) (pf : TL.Proof.T.proof) (depth : int) =
  let open TL.Proof.T in
  match TL.Property.unwrap pf with
  | Omitted Implicit ->
      [ ca_omitted ~uri ~ps; ca_to_steps ~uri ~ps ~cx ~pf ~depth ]
  | Omitted Explicit | Omitted (Elsewhere _) ->
      [ ca_to_steps ~uri ~ps ~cx ~pf ~depth ]
  | Steps ([], _) ->
      (* TODO: Drop one level. *)
      []
  | Steps (_, _) -> []
  | Obvious | By (_, _) -> [ ca_to_steps ~uri ~ps ~cx ~pf ~depth ]
  | Error _ -> []

(** Creates a rewrite for the proof of the current step, replacing it with BY
    and the step names listed. *)
let ps_proof_rewrite ps cx step_names =
  let r =
    Range.of_points
      (Range.from (PS.head_range ps |> Range.make_after))
      (Range.till (PS.full_range ps))
  in
  let ps_proof_new =
    TL.Proof.T.By
      ( {
          facts =
            List.map
              (fun sn ->
                TL.Property.noprops
                  (TL.Expr.T.Opaque (TL.Proof.T.string_of_stepno sn)))
              step_names;
          defs = [];
        },
        false )
    |> TL.Property.noprops
  in
  let t = Fmt.str " %a\n" (pp_proof cx) ps_proof_new in
  (r, t)

(** Create code action for a goal in the form of universal quantification. *)
let cas_of_goal_forall (uri : LspT.DocumentUri.t) (ps : PS.t) (ps_parent : PS.t)
    (cx : TL.Expr.T.ctx) (bs : TL.Expr.T.bound list) =
  let title = "Decompose goal (\\A)" in
  let step = TL.Proof.T.Take bs |> TL.Property.noprops in
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
  let title = "Decompose goal (\\E)" in
  let step_names = Seq_acc.make (PS.sub_step_name_seq ps_parent) in
  let bs_unditto = TL.Expr.T.unditto bs in
  let noprops = TL.Property.noprops in
  let steps_def =
    bs
    |> List.map @@ fun (b_name, _, _) ->
       (* TODO: Pick unique names. *)
       let step_no = PS.sub_step_unnamed ps_parent in
       let step =
         TL.Proof.T.Define
           [
             TL.Expr.T.Operator
               ( b_name,
                 TL.Expr.T.String "TODO: Replace this with actual witness"
                 |> noprops )
             |> noprops;
           ]
         |> noprops
       in
       (step_no, step)
  in
  let step_hide =
    let defs =
      bs
      |> List.map @@ fun (b_name, _, _) ->
         TL.Proof.T.Dvar (TL.Property.unwrap b_name) |> noprops
    in
    let step_no = PS.sub_step_unnamed ps_parent in
    let step = TL.Proof.T.Hide { facts = []; defs } |> noprops in
    (step_no, step)
  in
  let steps_pf_dom =
    bs_unditto
    |> List.filter_map @@ fun (b_name, _, b_dom) ->
       match b_dom with
       | TL.Expr.T.Domain dom_expr ->
           let active =
             TL.Expr.T.Apply
               ( TL.Expr.T.Internal TL.Builtin.Mem |> noprops,
                 [
                   TL.Expr.T.Opaque (TL.Property.unwrap b_name) |> noprops;
                   dom_expr;
                 ] )
             |> noprops
           in
           let step =
             TL.Proof.T.Assert
               ( { context = TL.Util.Deque.empty; active },
                 TL.Proof.T.(Omitted Implicit) |> noprops )
             |> noprops
           in
           let step_no = Seq_acc.take step_names in
           Some (step_no, step)
       | TL.Expr.T.No_domain | TL.Expr.T.Ditto -> None
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
      |> List.map @@ fun (b_name, _, b_dom) ->
         match b_dom with
         | TL.Expr.T.No_domain | TL.Expr.T.Ditto ->
             TL.Expr.T.Opaque (TL.Property.unwrap b_name) |> noprops
         | TL.Expr.T.Domain dom ->
             TL.Expr.T.Apply
               ( TL.Expr.T.Internal TL.Builtin.Mem |> noprops,
                 [
                   TL.Expr.T.Opaque (TL.Property.unwrap b_name) |> noprops; dom;
                 ] )
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
  let step_names = Seq_acc.make (PS.sub_step_name_seq ps_parent) in
  let add_steps_rewrite =
    let ps_proof = PS.proof ps |> Option.get in
    flatten_op_list Conj op_args
    |> List.map (fun op ->
           let step_no = Seq_acc.take step_names in
           let step =
             TL.Proof.T.Assert
               ({ context = TL.Util.Deque.empty; active = op }, ps_proof)
             |> TL.Property.noprops
           in
           (step_no, step))
    |> pp_proof_steps_before ps cx
  in
  let ps_proof_rewrite = ps_proof_rewrite ps cx (Seq_acc.acc step_names) in
  let ca =
    ca_edits ~uri ~title:"Decompose goal (/\\)"
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
    let step_names = Seq_acc.make (PS.sub_step_name_seq ps_parent) in
    let step_no = Seq_acc.take step_names in
    let other_negated =
      disjuncts
      |> List.filteri (fun i _ -> i != disjunct_pos)
      |> List.mapi (fun i disjunct ->
             (* TODO: Drop existing negation, if there exist instead of adding yet another. *)
             let expr =
               TL.Expr.T.Apply
                 ( TL.(Expr.T.Internal Builtin.Neg) |> TL.Property.noprops,
                   [ disjunct ] )
               |> TL.Property.noprops
             in
             TL.Expr.T.(Fact (expr, Visible, NotSet))
             |> TL.Property.noprops
             |> TL.Expr.Subst.(app_hyp (shift i)))
    in
    let disjunct =
      disjunct |> TL.Expr.Subst.(app_expr (shift (List.length other_negated)))
    in
    let step =
      TL.Proof.T.Suffices
        ( { context = TL.Util.Deque.of_list other_negated; active = disjunct },
          ps_proof )
      |> TL.Property.noprops
    in
    let new_step_rewrite = pp_proof_steps_before ps cx [ (step_no, step) ] in
    let ps_proof_rewrite = ps_proof_rewrite ps cx [ step_no ] in
    ca_edits ~uri
      ~title:(Fmt.str "Decompose goal (\\/, case %d)" (disjunct_pos + 1))
      ~edits:[ new_step_rewrite; ps_proof_rewrite ]
  in
  List.mapi disjunct_ca disjuncts

(* A chain of equivalences is replaced with a list of circular implications. *)
let cas_of_goal_equiv (uri : LspT.DocumentUri.t) (ps : PS.t) (ps_parent : PS.t)
    cx op_args =
  let step_names = Seq_acc.make (PS.sub_step_name_seq ps_parent) in
  let add_steps_rewrite =
    let ps_proof = PS.proof ps |> Option.get in
    let op_args = flatten_op_list Equiv op_args in
    let next_arg i = List.nth op_args ((i + 1) mod List.length op_args) in
    op_args
    |> List.mapi (fun i op ->
           let step_no = Seq_acc.take step_names in
           let step_goal =
             TL.Expr.T.Apply
               ( TL.Expr.T.Internal TL.Builtin.Implies |> TL.Property.noprops,
                 [ op; next_arg i ] )
             |> TL.Property.noprops
           in
           let step =
             TL.Proof.T.Assert
               ({ context = TL.Util.Deque.empty; active = step_goal }, ps_proof)
             |> TL.Property.noprops
           in
           (step_no, step))
    |> pp_proof_steps_before ps cx
  in
  let ps_proof_rewrite = ps_proof_rewrite ps cx (Seq_acc.acc step_names) in
  let ca =
    ca_edits ~uri ~title:"Decompose goal (<=>)"
      ~edits:[ add_steps_rewrite; ps_proof_rewrite ]
  in
  [ ca ]

(** Propose proof decomposition CodeActions by the structure of the goal. *)
let cas_by_goal (uri : LspT.DocumentUri.t) (ps : PS.t) (ps_parent : PS.t)
    (o : TL.Proof.T.obligation) (depth : int) =
  let rec match_goal cx (ex : TL.Expr.T.expr) =
    match ex.core with
    | TL.Expr.T.Apply (op, op_args) -> (
        match op.core with
        | TL.Expr.T.Internal bi -> (
            match bi with
            | TL.Builtin.Implies ->
                (* TODO: Move to a separate function, get rid of the depth val. *)
                let antecedent = List.hd op_args in
                let new_ps = TL.Property.noprops (TL.Proof.T.Have antecedent) in
                let title = "Decompose goal (=>)" in
                let range = Range.make_before (PS.full_range ps) in
                let newText =
                  indent ps ~nested:false
                    (Fmt.str "<%d> %a\n" depth (pp_proof_step cx) new_ps)
                in
                let ca = ca_edit ~uri ~title ~range ~newText in
                [ ca ]
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
        | TL.Expr.T.And -> cas_of_goal_conj uri ps ps_parent cx exprs
        | TL.Expr.T.Or -> cas_of_goal_disj uri ps ps_parent cx exprs
        | TL.Expr.T.Refs -> [])
    | TL.Expr.T.Ix ix -> (
        let hyp = TL.Expr.T.get_val_from_id cx ix in
        let cx = TL.Expr.T.cx_front cx ix in
        match hyp.core with
        | TL.Expr.T.Fresh (_, _, _, _)
        | TL.Expr.T.FreshTuply (_, _)
        | TL.Expr.T.Flex _ ->
            []
        | TL.Expr.T.Defn (defn, _, _, _) -> (
            match defn.core with
            | TL.Expr.T.Operator (_, ex) -> match_goal cx ex
            | TL.Expr.T.Recursive (_, _)
            | TL.Expr.T.Instance (_, _)
            | TL.Expr.T.Bpragma (_, _, _) ->
                [])
        | TL.Expr.T.Fact (ex, _, _) -> match_goal cx ex)
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
  match_goal o.obl.core.context o.obl.core.active

(* Code Actions of Proof Step *)
let cas_of_ps (uri : LspT.DocumentUri.t) (ps : PS.t) (ps_parent : PS.t) =
  let open TL.Proof.T in
  let el, cx = PS.el ps in
  let cas_of_el_with_pf = cas_of_el_with_pf uri ps cx in
  let step_no s =
    match TL.Property.get s TL.Proof.T.Props.step with
    | Named (depth, _, _) | Unnamed (depth, _) -> depth
  in
  match el with
  | PS.El.Mutate _ | PS.El.Module _ -> []
  | PS.El.Theorem { orig_pf; _ } -> cas_of_el_with_pf orig_pf 0
  | PS.El.Step step -> (
      let step_no = step_no step in
      match TL.Property.unwrap step with
      | Assert (_, pf)
      | Suffices (_, pf)
      | Pcase (_, pf)
      | Pick (_, _, pf)
      | PickTuply (_, _, pf) ->
          cas_of_el_with_pf pf step_no
      | Hide _ | Define _
      | Use (_, _)
      | Have _ | Take _ | TakeTuply _ | Witness _ | Forget _ ->
          [])
  | PS.El.Qed qed_step ->
      let step_no = step_no qed_step in
      let cas_of_goal =
        PS.goal ps
        |> Option.fold ~none:[] ~some:(fun g ->
               cas_by_goal uri ps ps_parent g step_no)
      in
      let cas_of_pf =
        match TL.Property.unwrap qed_step with
        | Qed pf -> cas_of_el_with_pf pf step_no
      in
      List.concat [ cas_of_goal; cas_of_pf ]

let code_actions (uri : LspT.DocumentUri.t) (mule_ps : PS.t) (range : Range.t) :
    LspT.CodeAction.t list =
  match PS.locate_proof_path mule_ps range with
  | ps :: parent :: _ -> cas_of_ps uri ps parent
  | _ :: _ -> [] (* Module is the root, no decompositions there. *)
  | [] -> [] (* Should not be possible. *)
