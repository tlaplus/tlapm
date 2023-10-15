(* cSpell:words printexc recursives submod anoninst naxs pcase *)

(* Max number of unprocessed/pending versions to keep. *)
let keep_vsn_count = 50
let prover_mutex = Eio.Mutex.create ()

module OblRef = struct
  type t = int * int

  let compare (p_ref_a, obl_id_a) (p_ref_b, obl_id_b) =
    let p_ref_cmp = Stdlib.compare p_ref_a p_ref_b in
    if p_ref_cmp = 0 then Stdlib.compare obl_id_a obl_id_b else p_ref_cmp
end

module DocMap = Map.Make (Lsp.Types.DocumentUri)
module OblMap = Map.Make (OblRef)
module LspT = Lsp.Types
open Tlapm_lsp_prover
open Tlapm_lsp_prover.ToolboxProtocol

(* Proof step, as it is displayed in the editor. *)
module ProofStep = struct
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
    | Pending -> "Proof pending, press ctrl+g+g."
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

  let rec flatten pss =
    List.flatten (List.map (fun ps -> ps :: flatten ps.sub) pss)

  let q_range prop = TlapmRange.of_locus_opt (Tlapm_lib.Util.query_locus prop)

  let rec of_provable stm_range seq_range (proof : Tlapm_lib.Proof.T.proof) =
    (* let seq_range = q_range sequent.active in *)
    (* TODO: Consider the obligation loc. *)
    let sub, min_st, obl_loc = of_proof proof in
    let hdr_loc =
      match (stm_range, seq_range) with
      | Some stm_r, Some seq_r ->
          Some
            (TlapmRange.of_points (TlapmRange.from stm_r)
               (TlapmRange.till seq_r))
      | Some stm_r, None -> Some stm_r
      | None, Some seq_r -> Some seq_r
      | None, None -> None
    in
    { loc = stm_range; hdr_loc; obl_loc; state = min_st; sub }

  and of_proof (proof : Tlapm_lib.Proof.T.proof) =
    let open Tlapm_lib in
    let obl_loc = q_range proof in
    match Property.unwrap proof with
    | Proof.T.Obvious -> ([], Pending, obl_loc)
    | Proof.T.Omitted _ -> ([], Omitted, obl_loc)
    | Proof.T.By (_, _) -> ([], Pending, obl_loc)
    | Proof.T.Steps (steps, qed_step) -> (
        let sub = List.map of_step steps in
        let qed = of_qed_step qed_step in
        let sub = List.flatten (sub @ [ qed ]) in
        match min_s_of_t_list sub with
        | None -> (sub, Failed, obl_loc)
        | Some min_s -> (sub, min_s, obl_loc))
    | Proof.T.Error _ -> ([], Failed, obl_loc)

  and of_step (step : Tlapm_lib.Proof.T.step) =
    let open Tlapm_lib in
    match Property.unwrap step with
    | Proof.T.Hide _ -> []
    | Proof.T.Define _ -> []
    | Proof.T.Assert (sequent, proof) ->
        [ of_provable (q_range step) (q_range sequent.active) proof ]
    | Proof.T.Suffices (sequent, proof) ->
        [ of_provable (q_range step) (q_range sequent.active) proof ]
    | Proof.T.Pcase (expr, proof) ->
        [ of_provable (q_range step) (q_range expr) proof ]
    | Proof.T.Pick (_bounds, expr, proof) ->
        [ of_provable (q_range step) (q_range expr) proof ]
    | Proof.T.Use (_, _) -> []
    | Proof.T.Have _ -> []
    | Proof.T.Take _ -> []
    | Proof.T.Witness _ -> []
    | Proof.T.Forget _ -> []

  and of_qed_step (qed_step : Tlapm_lib.Proof.T.qed_step) =
    let loc = q_range qed_step in
    let hdr_loc =
      match loc with
      | Some loc ->
          let loc_from = TlapmRange.from loc in
          let loc_till = TlapmRange.p_add loc_from 0 (String.length "QED") in
          Some (TlapmRange.of_points loc_from loc_till)
      | None -> None
    in
    match Tlapm_lib.Property.unwrap qed_step with
    | Tlapm_lib.Proof.T.Qed proof ->
        (* TODO: QED has no locus, for some reason. Try to take proof loc at least. *)
        let hdr_loc =
          match hdr_loc with
          | None -> q_range proof
          | Some hdr_loc -> Some hdr_loc
        in
        let sub, state, obl_loc = of_proof proof in
        [ { loc; hdr_loc; obl_loc; state; sub } ]

  and of_module ?(acc = []) (mule : Tlapm_lib.Module.T.mule) =
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
            let ps = of_provable (q_range mod_unit) (q_range sq.active) prf in
            ps :: acc
        | Submod sm -> of_module ~acc sm
        | Mutate _ -> acc
        | Anoninst _ -> acc)
      acc mule_.body

  let rec with_tlapm_obligation (pss : t list) (obl : tlapm_obligation) =
    let with_opt_min_s ps opt_sub_min_s =
      match opt_sub_min_s with
      | None -> ps
      | Some sub_min_s -> { ps with state = sub_min_s }
    in
    let upd ps =
      let sub = with_tlapm_obligation ps.sub obl in
      let sub_min_s = min_s_of_t_list sub in
      let ps = { ps with sub } in
      match ps.obl_loc with
      | None -> with_opt_min_s ps sub_min_s
      | Some ps_obl_loc ->
          if TlapmRange.from ps_obl_loc = TlapmRange.from obl.loc then
            with_opt_min_s
              { ps with state = s_of_tlapm_obl_state obl.status }
              sub_min_s
          else with_opt_min_s ps sub_min_s
    in
    List.map upd pss
end

(** Versions that are collected after the last prover launch or client
    asks for diagnostics. We store some limited number of versions here,
    just to cope with async events from the client. *)
module TV = struct
  type t = {
    text : string; (* Contents if the file at the specific version. *)
    version : int;
  }

  let make txt vsn = { text = txt; version = vsn }
end

(** Actual state of the document. *)
module TA = struct
  type t = {
    doc_vsn : TV.t;
    p_ref : int;
    mule : (Tlapm_lib.Module.T.mule, unit) result option;
    nts : tlapm_notif list;
    obs : tlapm_obligation OblMap.t;
    pss : ProofStep.t list;
  }

  let make tv =
    {
      doc_vsn = tv;
      p_ref = 0;
      mule = None;
      nts = [];
      obs = OblMap.empty;
      pss = [];
    }
end

(** Represents a document identified by its uri. It can contain multiple versions and all the related info. *)
module TD = struct
  type t = {
    pending : TV.t list; (* All the received but not yet processed versions. *)
    actual : TA.t option; (* Already processed version. *)
    last_p_ref : int; (* Counter for the proof runs. *)
  }

  let make tv = { pending = [ tv ]; actual = None; last_p_ref = 0 }
end

type tk = Lsp.Types.DocumentUri.t
type t = TD.t DocMap.t

type proof_res =
  int * tlapm_obligation list * tlapm_notif list * ProofStep.t list

let empty = DocMap.empty

(* Just record the text. It will be processed later, when a prover
   command or diagnostics query is issued by the client. *)
let add docs uri vsn txt =
  let rev = TV.make txt vsn in
  let drop_unused =
    List.filter (fun (pv : TV.t) -> pv.version < vsn - keep_vsn_count)
  in
  let upd = function
    | None -> Some (TD.make rev)
    | Some (d : TD.t) -> Some { d with pending = rev :: drop_unused d.pending }
  in
  DocMap.update uri upd docs

let rem docs uri = DocMap.remove uri docs

let latest_vsn docs uri =
  match DocMap.find_opt uri docs with
  | None -> None
  | Some TD.{ actual; pending = []; _ } -> (
      match actual with
      | Some { doc_vsn; _ } -> Some doc_vsn.version
      | None -> None)
  | Some TD.{ pending = dv :: _; _ } -> Some dv.version

let with_actual doc uri docs f act pending =
  let doc = TD.{ doc with pending; actual = Some act } in
  let doc, act, res = f doc act in
  let doc = TD.{ doc with actual = Some act } in
  let docs = DocMap.add uri doc docs in
  (docs, res)

(* Here we merge pending versions with the actual and then run
   the supplied function on the prepared doc info. *)
let with_doc_vsn docs uri vsn f =
  match DocMap.find_opt uri docs with
  | None -> (docs, None)
  | Some (TD.{ pending; actual; _ } as doc) -> (
      let fresh_active v = TA.make v in
      let merge_into (v : TV.t) (a : TA.t) =
        let diff_pos = TlapmRange.first_diff_pos a.doc_vsn.text v.text in
        let before_change loc = not (TlapmRange.before diff_pos loc) in
        let obs =
          OblMap.filter
            (fun _ (o : tlapm_obligation) -> before_change o.loc)
            a.obs
        in
        let nts =
          List.filter (fun (n : tlapm_notif) -> before_change n.loc) a.nts
        in
        { a with doc_vsn = v; obs; nts }
      in
      let rec drop_after_vsn = function
        | [] -> (None, [])
        | (pv : TV.t) :: pvs ->
            if pv.version = vsn then (Some pv, [])
            else
              let res, pvs = drop_after_vsn pvs in
              (res, pv :: pvs)
      in
      match actual with
      | Some ({ doc_vsn = adv; _ } as actual) when adv.version = vsn ->
          with_actual doc uri docs f actual pending
      | _ -> (
          let selected, pending = drop_after_vsn pending in
          match selected with
          | None -> (docs, None)
          | Some selected ->
              let act =
                match actual with
                | None -> fresh_active selected
                | Some act -> merge_into selected act
              in
              let act = { act with mule = None } in
              with_actual doc uri docs f act pending))

let try_parse_anyway_locked uri (act : TA.t) =
  let v = act.doc_vsn in
  match
    Tlapm_lib.module_of_string v.text (Lsp.Types.DocumentUri.to_path uri)
  with
  | Ok mule ->
      let pss = ProofStep.of_module mule in
      let pss =
        (* Apply retained obligation states. *)
        OblMap.fold
          (fun _ ob pss -> ProofStep.with_tlapm_obligation pss ob)
          act.obs pss
      in
      { act with mule = Some (Ok mule); pss; nts = [] }
  | Error (loc_opt, msg) ->
      {
        act with
        mule = Some (Error ());
        nts = [ ToolboxProtocol.notif_of_loc_msg loc_opt msg ];
      }

let try_parse_anyway uri act =
  Eio.Mutex.use_rw ~protect:true prover_mutex @@ fun () ->
  try_parse_anyway_locked uri act

let try_parse uri (act : TA.t) =
  match act with
  | { mule = None; _ } -> try_parse_anyway uri act
  | { mule = Some _; _ } -> act

let proof_res (act : TA.t) =
  let obs_list = List.map snd (OblMap.to_list act.obs) in
  (act.p_ref, obs_list, act.nts, ProofStep.flatten act.pss)

(* Push specific version to the actual, increase the proof_rec and clear the notifications. *)
let prepare_proof docs uri vsn range :
    t * (int * string * TlapmRange.t * proof_res) option =
  with_doc_vsn docs uri vsn @@ fun (doc : TD.t) (act : TA.t) ->
  let act = try_parse uri act in
  match act.mule with
  | None | Some (Error _) -> (doc, act, None)
  | Some (Ok _) ->
      let next_p_ref = doc.last_p_ref + 1 in
      let doc = { doc with last_p_ref = next_p_ref } in
      let act = { act with p_ref = next_p_ref; nts = [] } in
      let pss_locs = List.map (fun (ps : ProofStep.t) -> ps.loc) act.pss in
      let pss_locs = List.filter_map (fun ps -> ps) pss_locs in
      (* TODO: Locate properly the most detailed proof step here. *)
      let p_range = TlapmRange.covered_or_empty range pss_locs in
      (doc, act, Some (next_p_ref, act.doc_vsn.text, p_range, proof_res act))

let add_obl docs uri vsn p_ref (obl : tlapm_obligation) =
  with_doc_vsn docs uri vsn @@ fun (doc : TD.t) (act : TA.t) ->
  if act.p_ref = p_ref then
    let drop_older_intersecting (o_pr, _o_id) (o : tlapm_obligation) =
      o_pr = p_ref || not (TlapmRange.lines_intersect obl.loc o.loc)
    in
    let obs = OblMap.add (p_ref, obl.id) obl act.obs in
    let obs = OblMap.filter drop_older_intersecting obs in
    let pss = ProofStep.with_tlapm_obligation act.pss obl in
    let act = { act with obs; pss } in
    (doc, act, Some (proof_res act))
  else (doc, act, None)

let add_notif docs uri vsn p_ref notif =
  with_doc_vsn docs uri vsn @@ fun (doc : TD.t) (act : TA.t) ->
  if act.p_ref = p_ref then
    let nts = notif :: act.nts in
    let act = { act with nts; obs = OblMap.empty } in
    (doc, act, Some (proof_res act))
  else (doc, act, None)

let get_proof_res docs uri vsn =
  with_doc_vsn docs uri vsn @@ fun doc act ->
  let act = try_parse uri act in
  (doc, act, Some (proof_res act))

let get_proof_res_latest docs uri =
  match latest_vsn docs uri with
  | None -> (docs, None, None)
  | Some latest_vsn ->
      let docs, res = get_proof_res docs uri latest_vsn in
      (docs, Some latest_vsn, res)
