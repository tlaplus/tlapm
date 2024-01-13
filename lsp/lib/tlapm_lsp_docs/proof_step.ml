open Util
open Tlapm_lsp_prover
open Tlapm_lsp_prover.ToolboxProtocol

type s = Proved | Failed | Omitted | Missing | Pending | Progress

let s_of_tlapm_obl_state = function
  | ToolboxProtocol.ToBeProved -> Progress
  | ToolboxProtocol.BeingProved -> Pending
  | ToolboxProtocol.Normalized -> Progress
  | ToolboxProtocol.Proved -> Proved
  | ToolboxProtocol.Failed -> Failed
  | ToolboxProtocol.Interrupted -> Failed
  | ToolboxProtocol.Trivial -> Proved
  | ToolboxProtocol.Unknown _ -> Failed

let message_of_s = function
  | Failed -> "Proof failed."
  | Missing -> "Proof missing."
  | Omitted -> "Proof omitted."
  | Progress -> "Proving in progress."
  | Pending -> "Proof pending."
  | Proved -> "Proof checked successfully."

let order_of_s = function
  | Failed -> 0
  | Missing -> 1
  | Omitted -> 2
  | Progress -> 3
  | Pending -> 4
  | Proved -> 5

let s_of_order = function
  | 0 -> Failed
  | 1 -> Missing
  | 2 -> Omitted
  | 3 -> Progress
  | 4 -> Pending
  | 5 -> Proved
  | _ -> failwith "Impossible order"

let min_of_s a b = s_of_order (min (order_of_s a) (order_of_s b))

type t = {
  loc : TlapmRange.t option; (* Location if the entire step. *)
  hdr_loc : TlapmRange.t option; (* The location of the proof sequent.*)
  obl_loc : TlapmRange.t option; (* Where the obligation exists. *)
  obl_parsed : Obl_parsed.t; (* Obligation from the parser, if exist. *)
  obl_proofs : Obl_proofs.t option; (* The corresponding obligation info. *)
  state : s;
  sub : t list;
}

let min_s_of_t_list sub =
  match sub with
  | [] -> None
  | (first : t) :: _ ->
      let state =
        List.fold_left
          (fun st (sub : t) -> min_of_s st sub.state)
          first.state sub
      in
      Some state

let yojson_of_s = function
  | Proved -> `String "proved"
  | Failed -> `String "failed"
  | Omitted -> `String "omitted"
  | Missing -> `String "missing"
  | Pending -> `String "pending"
  | Progress -> `String "progress"

let yojson_of_t (t : t) =
  match t.hdr_loc with
  | None -> None
  | Some hdr_loc ->
      let obj =
        `Assoc
          [
            ("range", LspT.Range.yojson_of_t (TlapmRange.as_lsp_range hdr_loc));
            ("state", yojson_of_s t.state);
            ("hover", `String (message_of_s t.state));
          ]
      in
      Some obj

let tlaps_proof_obligation_state_of_t uri ps =
  let open Tlapm_lsp_structs in
  match ps.loc with
  | None -> None
  | Some ps_loc ->
      let some_str s = match s with None -> "?" | Some s -> s in
      let location =
        Location.make ~uri ~range:(TlapmRange.as_lsp_range ps_loc)
      in
      let obligation = some_str (Obl_parsed.text_normalized ps.obl_parsed) in
      let results =
        match ps.obl_proofs with
        | None -> []
        | Some oi ->
            List.map
              (fun (_, o) ->
                let prover = some_str o.prover in
                let status = message_of_s (s_of_tlapm_obl_state o.status) in
                let meth = some_str o.meth in
                let reason = o.reason in
                let obligation = o.obl in
                TlapsProofObligationResult.make ~prover ~meth ~status ~reason
                  ~obligation)
              (StrMap.to_list oi.by_prover)
      in
      Some (TlapsProofObligationState.make ~location ~obligation ~results)

let rec flatten pss =
  List.flatten (List.map (fun ps -> ps :: flatten ps.sub) pss)

let q_range prop = TlapmRange.of_locus_opt (Tlapm_lib.Util.query_locus prop)

let rec of_provable stm_range seq_range (proof : Tlapm_lib.Proof.T.proof)
    obs_map =
  let sub, min_st, obl_loc = of_proof proof obs_map in
  let hdr_loc =
    match (stm_range, seq_range) with
    | Some stm_r, Some seq_r ->
        Some
          (TlapmRange.of_points (TlapmRange.from stm_r) (TlapmRange.till seq_r))
    | Some stm_r, None -> Some stm_r
    | None, Some seq_r -> Some seq_r
    | None, None -> None
  in
  let obl_parsed =
    match obl_loc with
    | None -> Obl_parsed.make None
    | Some obl_loc -> Obl_parsed.make (RangeMap.find_opt obl_loc obs_map)
  in
  {
    loc = stm_range;
    hdr_loc;
    obl_loc;
    obl_parsed;
    obl_proofs = None;
    state = min_st;
    sub;
  }

and of_proof (proof : Tlapm_lib.Proof.T.proof) obs_map =
  let open Tlapm_lib in
  let obl_loc = q_range proof in
  match Property.unwrap proof with
  | Proof.T.Obvious -> ([], Pending, obl_loc)
  | Proof.T.Omitted _ -> ([], Omitted, obl_loc)
  | Proof.T.By (_, _) -> ([], Pending, obl_loc)
  | Proof.T.Steps (steps, qed_step) -> (
      let sub = List.map (fun s -> of_step s obs_map) steps in
      let qed = of_qed_step qed_step obs_map in
      let sub = List.flatten (sub @ [ qed ]) in
      match min_s_of_t_list sub with
      | None -> (sub, Failed, obl_loc)
      | Some min_s -> (sub, min_s, obl_loc))
  | Proof.T.Error _ -> ([], Failed, obl_loc)

and of_step (step : Tlapm_lib.Proof.T.step) obs_map =
  let open Tlapm_lib in
  match Property.unwrap step with
  | Proof.T.Hide _ -> []
  | Proof.T.Define _ -> []
  | Proof.T.Assert (sequent, proof) ->
      [ of_provable (q_range step) (q_range sequent.active) proof obs_map ]
  | Proof.T.Suffices (sequent, proof) ->
      [ of_provable (q_range step) (q_range sequent.active) proof obs_map ]
  | Proof.T.Pcase (expr, proof) ->
      [ of_provable (q_range step) (q_range expr) proof obs_map ]
  | Proof.T.Pick (_bounds, expr, proof) ->
      [ of_provable (q_range step) (q_range expr) proof obs_map ]
  | Proof.T.Use (_, _) -> []
  | Proof.T.Have _ -> []
  | Proof.T.Take _ -> []
  | Proof.T.Witness _ -> [] (* TODO: Form a step for this. *)
  | Proof.T.Forget _ -> []

and of_qed_step (qed_step : Tlapm_lib.Proof.T.qed_step) obs_map =
  match Tlapm_lib.Property.unwrap qed_step with
  | Tlapm_lib.Proof.T.Qed proof ->
      let open Tlapm_lib in
      let qed_loc = Property.query qed_step Proof.Parser.qed_loc_prop in
      let qed_range = TlapmRange.of_locus_opt qed_loc in
      [ of_provable (q_range qed_step) qed_range proof obs_map ]

and of_module (mule : Tlapm_lib.Module.T.mule) =
  match mule.core.stage with
  | Final fin ->
      let obs = fin.final_obs in
      let obs_map =
        RangeMap.of_list
          (List.filter_map
             (fun (o : Tlapm_lib.Proof.T.obligation) ->
               match q_range o.obl with
               | None -> None
               | Some o_range -> Some (o_range, o))
             (Array.to_list obs))
      in
      of_module_rec ~acc:[] mule obs_map
  | Parsed -> failwith "of_module, parsed"
  | _ -> failwith "of_module, non final"

and of_module_rec ?(acc = []) (mule : Tlapm_lib.Module.T.mule) obs_map =
  let open Tlapm_lib in
  let mule_ = Property.unwrap mule in
  List.fold_left
    (fun acc mod_unit ->
      let open Tlapm_lib.Module.T in
      match Property.unwrap mod_unit with
      | Constants _ -> acc
      | Recursives _ -> acc
      | Variables _ -> acc
      | Definition _ -> acc
      | Axiom _ -> acc
      | Theorem (_name, sq, _naxs, prf, _prf_orig, _sum) ->
          let ps =
            of_provable (q_range mod_unit) (q_range sq.active) prf obs_map
          in
          ps :: acc
      | Submod sm -> of_module_rec ~acc sm obs_map
      | Mutate _ -> acc
      | Anoninst _ -> acc)
    acc mule_.body

let rec with_tlapm_obligation (pss : t list) (oi : Obl_proofs.t) =
  (* Here we derive a state for a structured proof step as a worst state of its steps. *)
  let with_opt_min_s ps opt_sub_min_s =
    match opt_sub_min_s with
    | None -> ps
    | Some sub_min_s -> { ps with state = sub_min_s }
  in
  let upd ps =
    let sub = with_tlapm_obligation ps.sub oi in
    let sub_min_s = min_s_of_t_list sub in
    let ps = { ps with sub } in
    match ps.obl_loc with
    | None -> with_opt_min_s ps sub_min_s
    | Some ps_obl_loc ->
        if TlapmRange.from ps_obl_loc = TlapmRange.from (Obl_proofs.loc oi) then
          let state = s_of_tlapm_obl_state (Obl_proofs.latest oi).status in
          with_opt_min_s { ps with state; obl_proofs = Some oi } sub_min_s
        else with_opt_min_s ps sub_min_s
  in
  List.map upd pss

let with_tlapm_obligations (pss : t list) (ois : Obl_proofs.t OblMap.t) =
  OblMap.fold (fun _ ob pss -> with_tlapm_obligation pss ob) ois pss

let locate_proof_range (pss : t list) (input : TlapmRange.t) : TlapmRange.t =
  let rec collect pss =
    let for_each_ps_with_loc ps ps_loc =
      match TlapmRange.lines_intersect ps_loc input with
      | true -> (
          match collect ps.sub with
          | [] -> Some [ ps_loc ]
          | first :: _ as sub_locs -> (
              match TlapmRange.(line_from input < line_from first) with
              | true -> Some [ ps_loc ]
              | false -> Some sub_locs))
      | false -> None
    in
    let for_each_ps ps =
      match ps.loc with
      | None -> None
      | Some ps_loc -> for_each_ps_with_loc ps ps_loc
    in
    List.flatten (List.filter_map for_each_ps pss)
  in
  let pss_locs = collect pss in
  TlapmRange.lines_covered_or_all input pss_locs

let find_proof_step (pss : t list) (input : TlapmRange.t) =
  let rec find_first pss =
    let for_each_ps_with_loc ps ps_loc =
      match TlapmRange.lines_intersect ps_loc input with
      | true -> (
          match find_first ps.sub with
          | None -> Some ps
          | Some first -> Some first)
      | false -> None
    in
    let for_each_ps ps =
      match ps.loc with
      | None -> None
      | Some ps_loc -> for_each_ps_with_loc ps ps_loc
    in
    List.find_map for_each_ps pss
  in
  find_first pss

let%test_unit "some" =
  let mod_file = "test_obl_expand.tla" in
  let mod_text =
    String.concat "\n"
      [
        "---- MODULE test_obl_expand ----";
        "THEOREM FALSE";
        "    <1>1. TRUE";
        "    <1>q. QED BY <1>1";
        "====";
      ]
  in
  let mule = Result.get_ok (Tlapm_lib.module_of_string mod_text mod_file) in
  let rec print_rec prefix no ps =
    let prefix = Format.sprintf "%s.%d" prefix no in
    let obl_str =
      match Obl_parsed.text_normalized ps.obl_parsed with
      | None -> "none"
      | Some o -> o
    in
    let obl_loc =
      match ps.obl_loc with
      | None -> "none"
      | Some l -> TlapmRange.string_of_range l
    in
    let hdr_loc =
      match ps.hdr_loc with
      | None -> "none"
      | Some l -> TlapmRange.string_of_range l
    in
    Format.printf "%s [hdr=%s, obl=%s] %s --> %s\n" prefix hdr_loc obl_loc
      (Obl_parsed.type_str ps.obl_parsed)
      obl_str;
    List.iteri (print_rec prefix) ps.sub
  in
  let pss = of_module mule in
  List.iteri (print_rec "test") pss;
  match flatten pss with
  | [ _theorem; _step11; step1q; _step1q_by ] -> (
      match Obl_parsed.text_normalized step1q.obl_parsed with
      | Some "ASSUME TRUE \nPROVE  FALSE" -> ()
      | Some s -> failwith (Format.sprintf "Unexpected %s" s)
      | None -> failwith "Unexpected none")
  | pss ->
      failwith
        (Format.sprintf "unexpected, number of steps=%d" (List.length pss))
