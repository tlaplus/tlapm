open Util

(** List expandable names in the expression and its context. *)
let expandable_names (cx : TL.Expr.T.ctx) (ex : TL.Expr.T.expr) : string list =
  let open TL.Expr in
  let names = ref StringSet.empty in
  let add_name n = names := StringSet.add n !names in
  let visitor =
    object (_self : 'self)
      inherit [unit] Visit.iter as super

      method! expr (cx : unit Visit.scx) (e : T.expr) =
        (match e.core with
        | T.Opaque name -> add_name name
        | T.Ix ix -> (
            let hyp = T.get_val_from_id (snd cx) ix in
            let cx = T.cx_front (snd cx) ix in
            match hyp |> unwrap with
            | T.Fresh (_, _, _, _) | T.FreshTuply (_, _) | T.Flex _ -> ()
            | T.Defn (defn, _, T.Visible, _) ->
                ignore (super#defn ((), cx) defn)
            | T.Defn (_, _, T.Hidden, _) -> add_name (T.hyp_name hyp)
            | T.Fact (ex, T.Visible, _) -> super#expr ((), cx) ex
            | T.Fact (_, T.Hidden, _) -> ())
        | T.Internal _
        | T.Lambda (_, _)
        | T.Sequent _
        | T.Bang (_, _)
        | T.Apply (_, _)
        | T.With (_, _)
        | T.If (_, _, _)
        | T.List (_, _)
        | T.Let (_, _)
        | T.Quant (_, _, _)
        | T.QuantTuply (_, _, _)
        | T.Tquant (_, _, _)
        | T.Choose (_, _, _)
        | T.ChooseTuply (_, _, _)
        | T.SetSt (_, _, _)
        | T.SetStTuply (_, _, _)
        | T.SetOf (_, _)
        | T.SetOfTuply (_, _)
        | T.SetEnum _ | T.Product _ | T.Tuple _
        | T.Fcn (_, _)
        | T.FcnTuply (_, _)
        | T.FcnApp (_, _)
        | T.Arrow (_, _)
        | T.Rect _ | T.Record _
        | T.Except (_, _)
        | T.Dot (_, _)
        | T.Sub (_, _, _)
        | T.Tsub (_, _, _)
        | T.Fair (_, _, _)
        | T.Case (_, _)
        | T.String _
        | T.Num (_, _)
        | T.At _
        | T.Parens (_, _) ->
            ());
        super#expr cx e
    end
  in
  let rec traverse_cx cx =
    match TL.Util.Deque.rear cx with
    | None -> ()
    | Some (cx, hyp) ->
        (match hyp |> unwrap with
        | T.Fresh (_, _, _, _)
        | T.FreshTuply (_, _)
        | T.Flex _
        | T.Defn (_, _, _, _) ->
            ()
        | T.Fact (_, _, _) -> ignore (visitor#hyp ((), cx) hyp));
        traverse_cx cx
  in
  visitor#expr ((), cx) ex;
  traverse_cx cx;
  StringSet.to_list !names |> List.sort String.compare

(** Propose expand actions for all the definitions that are visible, but not yet
    expanded.

    TODO: "Expand all definitions". *)
let cas_def_expand ~uri ~(ps : PS.t) ~cx ~by ~(sq : TL.Expr.T.sequent) =
  expandable_names sq.context sq.active
  |> List.map @@ fun def_name ->
     let usable, only = by in
     let usable = usable |> Usable.add_defs_str [ def_name ] in
     let new_pf = TL.Proof.T.By (usable, only) |> noprops in
     let range, newText = ps_proof_rewrite ps cx (`Proof new_pf) in
     ca_edit ~uri ~title:(Fmt.str "→ Expand %s" def_name) ~range ~newText
