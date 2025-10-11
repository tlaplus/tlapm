module PS = Docs.Proof_step
module TL = Tlapm_lib
module LspT = Lsp.Types
module StringSet = Set.Make (String)

let noprops = TL.Property.noprops
let unwrap = TL.Property.unwrap

let expand_expr_ref cx ix f =
  (* Fmt.epr "XXX: @[expand_expr_ref by ix=%d@]@." ix; *)
  let hyp = TL.Expr.T.get_val_from_id cx ix in
  let cx = TL.Expr.T.cx_front cx ix in
  match hyp.core with
  | TL.Expr.T.Fresh (_, _, _, _)
  | TL.Expr.T.FreshTuply (_, _)
  | TL.Expr.T.Flex _ ->
      []
  | TL.Expr.T.Defn (defn, _, Visible, _) -> (
      match defn.core with
      | TL.Expr.T.Operator (_, ex) -> f cx ex
      | TL.Expr.T.Recursive (_, _)
      | TL.Expr.T.Instance (_, _)
      | TL.Expr.T.Bpragma (_, _, _) ->
          [])
  | TL.Expr.T.Defn (_, _, _, _) -> []
  | TL.Expr.T.Fact (ex, Visible, _) -> f cx ex
  | TL.Expr.T.Fact (_, _, _) -> []

let join_exs ~unit ~op exs =
  let open TL.Expr.T in
  let ex =
    exs
    |> List.fold_left
         (fun acc ex ->
           match acc with
           | None -> Some ex
           | Some acc -> Some (Apply (op, [ acc; ex ]) |> noprops))
         None
  in
  Option.value ~default:unit ex

let make_disjunction exs =
  let open TL.Expr.T in
  let open TL.Builtin in
  join_exs ~unit:(Internal FALSE |> noprops) ~op:(Internal Disj |> noprops) exs

let make_conjunction exs =
  let open TL.Expr.T in
  let open TL.Builtin in
  join_exs ~unit:(Internal TRUE |> noprops) ~op:(Internal Conj |> noprops) exs

let expand_sub modal_op action_ex subscript_ex =
  let open TL.Expr.T in
  let open TL.Builtin in
  let unchanged =
    Apply (Internal UNCHANGED |> noprops, [ subscript_ex ]) |> noprops
  in
  match modal_op with
  | TL.Expr.T.Box -> make_disjunction [ action_ex; unchanged ]
  | TL.Expr.T.Dia ->
      let changed = Apply (Internal Neg |> noprops, [ unchanged ]) |> noprops in
      make_conjunction [ action_ex; changed ]

type flatten_by = Conj | Disj | Equiv | Implies

let rec flatten_op_list (by : flatten_by) (exs : TL.Expr.T.expr list) :
    TL.Expr.T.expr list =
  exs |> List.map (fun arg -> flatten_op by arg) |> List.flatten

and flatten_op (by : flatten_by) (ex : TL.Expr.T.expr) : TL.Expr.T.expr list =
  let open TL.Expr.T in
  let open TL.Builtin in
  match ex.core with
  | Apply (op, args) -> (
      match op.core with
      | Internal bi -> (
          match bi with
          | Conj when by = Conj -> flatten_op_list by args
          | Disj when by = Disj -> flatten_op_list by args
          | Equiv when by = Equiv -> flatten_op_list by args
          | Implies when by = Implies -> flatten_op_list by args
          | _ -> [ ex ])
      | _ -> [ ex ])
  | List (bullet, list) -> (
      match bullet with
      | And when by = Conj -> flatten_op_list by list
      | Refs when by = Conj -> flatten_op_list by list
      | Or when by = Disj -> flatten_op_list by list
      | _ -> [ ex ])
  | Sub (modal_op, action_ex, subscript_ex) -> (
      match modal_op with
      | Box when by = Disj ->
          flatten_op_list by [ expand_sub modal_op action_ex subscript_ex ]
      | Dia when by = Conj ->
          flatten_op_list by [ expand_sub modal_op action_ex subscript_ex ]
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

let fmt_cx cx =
  let fcx = TL.Ctx.dot |> TL.Ctx.with_try_print_src in
  let fcx =
    (* Push all the names known in the context to have proper
    suffixes _1, _2, ... for newly introduced identifiers. *)
    TL.Util.Deque.fold_left
      (fun fcx (hyp : TL.Expr.T.hyp) ->
        match hyp.core with
        | TL.Expr.T.Flex name | TL.Expr.T.Fresh (name, _, _, _) ->
            TL.Ctx.push fcx (unwrap name)
        | TL.Expr.T.FreshTuply (names, _) ->
            List.fold_right
              (fun name fcx -> TL.Ctx.push fcx (unwrap name))
              names fcx
        | TL.Expr.T.Defn (defn, _, _, _) -> (
            match defn.core with
            | TL.Expr.T.Recursive (name, _)
            | TL.Expr.T.Operator (name, _)
            | TL.Expr.T.Instance (name, _)
            | TL.Expr.T.Bpragma (name, _, _) ->
                TL.Ctx.push fcx (unwrap name))
        | TL.Expr.T.Fact (_, _, _) -> TL.Ctx.bump fcx)
      fcx cx
  in
  (cx, fcx)

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

(** Produce new unique name in the context (can be obtained by calling fmt_cx).
    The argument [name] is a base for generating the identifier. It might be
    returned as is, of suffixed with some number. *)
let fresh_ident (fmt_cx : TL.Expr.T.ctx * int TL.Ctx.ctx) (name : string) :
    string =
  let _ecx, fcx = fmt_cx in
  TL.Ctx.push fcx name |> TL.Ctx.front |> TL.Ctx.string_of_ident

(* Helpers for constructing code actions. *)

let ca_edit ~uri ~title ~range ~newText =
  let edit = LspT.TextEdit.create ~newText ~range:(Range.as_lsp_range range) in
  let edit = LspT.WorkspaceEdit.create ~changes:[ (uri, [ edit ]) ] () in
  LspT.CodeAction.create ~title ~edit ~kind:LspT.CodeActionKind.Refactor ()

let ca_edits ~uri ~title ~edits =
  let edits =
    List.map
      (fun (r, t) ->
        LspT.TextEdit.create ~newText:t ~range:(Range.as_lsp_range r))
      edits
  in
  let edit = LspT.WorkspaceEdit.create ~changes:[ (uri, edits) ] () in
  LspT.CodeAction.create ~title ~edit ()

(** Creates a rewrite for the proof of the current step, replacing it with BY
    and the step names listed. *)
let ps_proof_rewrite ps cx step_info =
  let r =
    Range.of_points
      (Range.from (PS.head_range ps |> Range.make_after))
      (Range.till (PS.full_range ps |> Range.with_end_line))
  in
  let ps_proof_new =
    match step_info with
    | `StepNames step_names ->
        TL.Proof.T.By
          ( {
              facts =
                List.map
                  (fun sn ->
                    TL.Expr.T.Opaque (TL.Proof.T.string_of_stepno sn) |> noprops)
                  step_names;
              defs = [];
            },
            false )
        |> noprops
    | `Usable us -> TL.Proof.T.By (us, false) |> noprops
    | `Proof pf -> pf
  in
  let t = Fmt.str " %a\n" (pp_proof cx) ps_proof_new in
  (r, t)
