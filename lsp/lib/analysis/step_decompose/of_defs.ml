open Util

(** List expandable names in the expression and its context. *)
let expandable_names (cx : TL.Expr.T.ctx) (ex : TL.Expr.T.expr) : string list =
  let names = ref StringSet.empty in
  let add_name n = names := StringSet.add n !names in
  let visitor =
    object (_self : 'self)
      inherit [unit] TL.Expr.Visit.iter as super

      method! expr (cx : unit TL.Expr.Visit.scx) (e : TL.Expr.T.expr) =
        (match e.core with
        | TL.Expr.T.Opaque name -> add_name name
        | TL.Expr.T.Ix ix -> (
            let hyp = TL.Expr.T.get_val_from_id (snd cx) ix in
            let cx = TL.Expr.T.cx_front (snd cx) ix in
            match hyp |> unwrap with
            | TL.Expr.T.Fresh (_, _, _, _)
            | TL.Expr.T.FreshTuply (_, _)
            | TL.Expr.T.Flex _ ->
                ()
            | TL.Expr.T.Defn (defn, _, TL.Expr.T.Visible, _) ->
                ignore (super#defn ((), cx) defn)
            | TL.Expr.T.Defn (_, _, TL.Expr.T.Hidden, _) ->
                add_name (TL.Expr.T.hyp_name hyp)
            | TL.Expr.T.Fact (ex, TL.Expr.T.Visible, _) ->
                super#expr ((), cx) ex
            | TL.Expr.T.Fact (_, TL.Expr.T.Hidden, _) -> ())
        | TL.Expr.T.Internal _
        | TL.Expr.T.Lambda (_, _)
        | TL.Expr.T.Sequent _
        | TL.Expr.T.Bang (_, _)
        | TL.Expr.T.Apply (_, _)
        | TL.Expr.T.With (_, _)
        | TL.Expr.T.If (_, _, _)
        | TL.Expr.T.List (_, _)
        | TL.Expr.T.Let (_, _)
        | TL.Expr.T.Quant (_, _, _)
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
            ());
        super#expr cx e
    end
  in
  let rec traverse_cx cx =
    match TL.Util.Deque.rear cx with
    | None -> ()
    | Some (cx, hyp) ->
        (match hyp |> unwrap with
        | TL.Expr.T.Fresh (_, _, _, _)
        | TL.Expr.T.FreshTuply (_, _)
        | TL.Expr.T.Flex _
        | TL.Expr.T.Defn (_, _, _, _) ->
            ()
        | TL.Expr.T.Fact (_, _, _) -> ignore (visitor#hyp ((), cx) hyp));
        traverse_cx cx
  in
  visitor#expr ((), cx) ex;
  traverse_cx cx;
  StringSet.to_list !names |> List.sort String.compare

(** Propose expand actions for all the definitions that are visible, but not yet
    expanded. *)
let cas_def_expand ~uri ~(ps : PS.t) ~cx ~by ~(sq : TL.Expr.T.sequent) =
  expandable_names sq.context sq.active
  |> List.map @@ fun def_name ->
     let usable, only = by in
     let usable = usable |> Usable.add_defs_str [ def_name ] in
     let new_pf = TL.Proof.T.By (usable, only) |> noprops in
     let range, newText = ps_proof_rewrite ps cx (`Proof new_pf) in
     ca_edit ~uri ~title:(Fmt.str "→ Expand %s" def_name) ~range ~newText
