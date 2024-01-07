(* cSpell:words recursives submod anoninst naxs pcase *)

(* Max number of unprocessed/pending versions to keep. *)
let keep_vsn_count = 50
let prover_mutex = Eio.Mutex.create ()

(** Obligation reference consists of the proof session reference (p_ref)
    and the obligation id (obl_id) as assigned by the TLAPS. This reference
    is unique across proof attempts.
    *)
module OblRef = struct
  type t = { p_ref : int; obl_id : int }

  let make ~p_ref ~obl_id = { p_ref; obl_id }

  let compare a b =
    let p_ref_cmp = Stdlib.compare a.p_ref b.p_ref in
    if p_ref_cmp = 0 then Stdlib.compare a.obl_id b.obl_id else p_ref_cmp
end

module LspT = Lsp.Types
module DocMap = Map.Make (LspT.DocumentUri)
module OblMap = Map.Make (OblRef)
module StrMap = Map.Make (String)
open Tlapm_lsp_prover
open Tlapm_lsp_prover.ToolboxProtocol

(** OblInfo collects related tlapm_obligation events into a single place.
    It maintains the general obligation info (initial) and the latest
    state for each of the provers.
    *)
module OblInfo = struct
  type t = {
    initial : tlapm_obligation;
    by_prover : tlapm_obligation StrMap.t;
    latest_prover : string option;
  }

  let make obl =
    { initial = obl; by_prover = StrMap.empty; latest_prover = None }

  let add_obl obl (oi : t) =
    match obl.prover with
    | None -> oi
    | Some prover ->
        let by_prover = StrMap.add prover obl oi.by_prover in
        { oi with by_prover; latest_prover = Some prover }

  let latest (oi : t) =
    match oi.latest_prover with
    | None -> oi.initial
    | Some prover -> StrMap.find prover oi.by_prover

  let loc (oi : t) = oi.initial.loc
end

(** Proof step, as it is displayed in the editor.
    The proof steps are obtained by parsing the the TLAPS source file.
    Later the proof obligation info is added to the tree as they are
    obtained from the prover.
    *)
module PS : sig
  type t

  val of_module : Tlapm_lib.Module.T.mule -> t list
  val with_tlapm_obligation : t list -> OblInfo.t -> t list
  val with_tlapm_obligations : t list -> OblInfo.t OblMap.t -> t list
  val locate_proof_range : t list -> TlapmRange.t -> TlapmRange.t
  val find_proof_step : t list -> TlapmRange.t -> t option
  val flatten : t list -> t list
  val yojson_of_t : t -> Yojson.Safe.t option

  val tlaps_proof_obligation_state_of_t :
    LspT.DocumentUri.t ->
    t ->
    Tlapm_lsp_structs.TlapsProofObligationState.t option
end = struct
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
    obl_info : OblInfo.t option; (* The corresponding obligation info. *)
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
    match (ps.loc, ps.obl_info) with
    | None, _ -> None
    | _, None -> None
    | Some ps_loc, Some oi ->
        let some_str s = match s with None -> "?" | Some s -> s in
        let location =
          Location.make ~uri ~range:(TlapmRange.as_lsp_range ps_loc)
        in
        let obligation = some_str oi.initial.obl in
        let results =
          List.map
            (fun (_, o) ->
              let status = message_of_s (s_of_tlapm_obl_state o.status) in
              let duration = 0 (* TODO: Track the timing. *) in
              TlapsProofObligationResult.make ~prover:(some_str o.prover)
                ~meth:(some_str o.meth) ~status ~duration ~obligation:o.obl)
            (StrMap.to_list oi.by_prover)
        in
        Some (TlapsProofObligationState.make ~location ~obligation ~results)

  let rec flatten pss =
    List.flatten (List.map (fun ps -> ps :: flatten ps.sub) pss)

  let q_range prop = TlapmRange.of_locus_opt (Tlapm_lib.Util.query_locus prop)

  let rec of_provable stm_range seq_range (proof : Tlapm_lib.Proof.T.proof) =
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
    { loc = stm_range; hdr_loc; obl_loc; obl_info = None; state = min_st; sub }

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
    match Tlapm_lib.Property.unwrap qed_step with
    | Tlapm_lib.Proof.T.Qed proof ->
        let open Tlapm_lib in
        let qed_loc = Property.query qed_step Proof.Parser.qed_loc_prop in
        let qed_range = TlapmRange.of_locus_opt qed_loc in
        [ of_provable (q_range qed_step) qed_range proof ]

  and of_module (mule : Tlapm_lib.Module.T.mule) = of_module_rec ~acc:[] mule

  and of_module_rec ?(acc = []) (mule : Tlapm_lib.Module.T.mule) =
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
        | Submod sm -> of_module_rec ~acc sm
        | Mutate _ -> acc
        | Anoninst _ -> acc)
      acc mule_.body

  let rec with_tlapm_obligation (pss : t list) (oi : OblInfo.t) =
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
          if TlapmRange.from ps_obl_loc = TlapmRange.from (OblInfo.loc oi) then
            let state = s_of_tlapm_obl_state (OblInfo.latest oi).status in
            with_opt_min_s { ps with state; obl_info = Some oi } sub_min_s
          else with_opt_min_s ps sub_min_s
    in
    List.map upd pss

  let with_tlapm_obligations (pss : t list) (ois : OblInfo.t OblMap.t) =
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
end

(** Proof results of a document. Includes the errors returned from the prover
    as well as all the proof steps with their current state.
    *)
module ProofRes = struct
  type t = {
    p_ref : int;
    obs : tlapm_obligation list;
    nts : tlapm_notif list;
    pss : PS.t list;
  }

  let empty = { p_ref = 0; obs = []; nts = []; pss = [] }

  let obs_done t =
    List.fold_left
      (fun acc ob ->
        if ToolboxProtocol.tlapm_obl_state_is_terminal ob.status then acc + 1
        else acc)
      0 t.obs
end

(** Versions that are collected after the last prover launch or client
    asks for diagnostics. We store some limited number of versions here,
    just to cope with async events from the client.
    *)
module TV : sig
  type t

  val make : string -> int -> t
  val text : t -> string
  val version : t -> int
  val diff_pos : t -> t -> TlapmRange.p
end = struct
  type t = {
    text : string; (* Contents if the file at the specific version. *)
    version : int;
  }

  let make txt vsn = { text = txt; version = vsn }
  let text tv = tv.text
  let version tv = tv.version
  let diff_pos a b = TlapmRange.first_diff_pos a.text b.text
end

(** Actual state of the document. *)
module TA : sig
  type t

  val make : TV.t -> t
  val vsn : t -> int
  val text : t -> string
  val merge_into : t -> TV.t -> t
  val try_parse : t -> LspT.DocumentUri.t -> t
  val proof_res : t -> ProofRes.t
  val prepare_proof : t -> LspT.DocumentUri.t -> int -> t option
  val locate_proof_range : t -> TlapmRange.t -> TlapmRange.t
  val get_obligation_state : t -> TlapmRange.t -> PS.t option
  val add_obl : t -> int -> tlapm_obligation -> t option
  val add_notif : t -> int -> tlapm_notif -> t option
  val terminated : t -> int -> t option
end = struct
  type t = {
    doc_vsn : TV.t;
    p_ref : int;
    mule : (Tlapm_lib.Module.T.mule, unit) result option;
    nts : tlapm_notif list;  (** Parsing errors and warnings. *)
    ois : OblInfo.t OblMap.t;
        (** A set of obligation results.
            It is set to empty, if any tlapm_notif is received. *)
    pss : PS.t list;
        (** Parsed document structure, a tree of proof steps.
            It is obtained by parsing the document and then updated
            when obligation proof states are received from the prover. *)
  }

  let make tv =
    {
      doc_vsn = tv;
      p_ref = 0;
      mule = None;
      nts = [];
      ois = OblMap.empty;
      pss = [];
    }

  let vsn act = TV.version act.doc_vsn
  let text act = TV.text act.doc_vsn

  (** Merge new version of the text (TV) into the existing actual version of the document. *)
  let merge_into (act : t) (v : TV.t) =
    let diff_pos = TV.diff_pos act.doc_vsn v in
    let before_change = TlapmRange.before diff_pos in
    let ois =
      OblMap.filter
        (fun _ (oi : OblInfo.t) -> before_change (OblInfo.loc oi))
        act.ois
    in
    let nts =
      List.filter (fun (n : tlapm_notif) -> before_change n.loc) act.nts
    in
    { act with doc_vsn = v; mule = None; ois; nts; pss = [] }

  let try_parse_anyway_locked uri (act : t) =
    let v = act.doc_vsn in
    match
      Tlapm_lib.module_of_string (TV.text v) (LspT.DocumentUri.to_path uri)
    with
    | Ok mule ->
        let pss = PS.of_module mule in
        let pss = PS.with_tlapm_obligations pss act.ois in
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

  let try_parse (act : t) uri =
    match act with
    | { mule = None; _ } -> try_parse_anyway uri act
    | { mule = Some _; _ } -> act

  let proof_res (act : t) : ProofRes.t =
    let latest_obl (_, oi) = OblInfo.latest oi in
    let obs_list = List.map latest_obl (OblMap.to_list act.ois) in
    {
      p_ref = act.p_ref;
      obs = obs_list;
      nts = act.nts;
      pss = PS.flatten act.pss;
    }

  let prepare_proof (act : t) uri next_p_ref =
    let act = try_parse act uri in
    match act.mule with
    | None | Some (Error ()) -> None
    | Some (Ok _mule) -> Some { act with p_ref = next_p_ref; nts = [] }

  let locate_proof_range act range = PS.locate_proof_range act.pss range
  let get_obligation_state act range = PS.find_proof_step act.pss range

  let add_obl (act : t) (p_ref : int) (obl : tlapm_obligation) =
    if act.p_ref = p_ref then
      let drop_older_intersecting (oRef : OblRef.t) (o : OblInfo.t) =
        oRef.p_ref = p_ref
        || not (TlapmRange.lines_intersect obl.loc (OblInfo.loc o))
      in
      let oi_ref = OblRef.make ~p_ref ~obl_id:obl.id in
      let oi =
        match OblMap.find_opt oi_ref act.ois with
        | None -> OblInfo.make obl
        | Some oi -> OblInfo.add_obl obl oi
      in
      let ois = OblMap.add oi_ref oi act.ois in
      let ois = OblMap.filter drop_older_intersecting ois in
      let pss = PS.with_tlapm_obligation act.pss oi in
      Some { act with ois; pss }
    else None

  let add_notif (act : t) p_ref notif =
    if act.p_ref = p_ref then
      let nts = notif :: act.nts in
      Some { act with nts; ois = OblMap.empty }
    else None

  let terminated (act : t) p_ref =
    if act.p_ref = p_ref then
      (* TODO: Mark intermediate obligation states as interrupted? *)
      Some act
    else None
end

(** Represents a document identified by its uri. It can contain multiple versions and all the related info. *)
module TD : sig
  type t

  val make : TV.t -> t
  val add : t -> TV.t -> t
  val latest_vsn : t -> int
  val set_actual_vsn : t -> int -> t option
  val with_actual : t -> (t -> TA.t -> t * TA.t * 'a) -> t * 'a
  val next_p_ref : t -> t * int
end = struct
  type t = {
    pending : TV.t list; (* All the received but not yet processed versions. *)
    actual : TA.t; (* Already processed version. *)
    last_p_ref : int; (* Counter for the proof runs. *)
  }

  let make tv = { pending = []; actual = TA.make tv; last_p_ref = 0 }

  let add doc tv =
    let drop_till = TV.version tv - keep_vsn_count in
    let drop_unused = List.filter (fun pv -> TV.version pv < drop_till) in
    { doc with pending = tv :: drop_unused doc.pending }

  let latest_vsn doc =
    match doc.pending with
    | [] -> TA.vsn doc.actual
    | latest :: _ -> TV.version latest

  let set_actual_vsn doc vsn =
    if TA.vsn doc.actual = vsn then Some doc
    else
      let rec drop_after_vsn = function
        | [] -> (None, [])
        | (pv : TV.t) :: pvs ->
            if TV.version pv = vsn then (Some pv, [])
            else
              let res, pvs = drop_after_vsn pvs in
              (res, pv :: pvs)
      in
      let selected, pending = drop_after_vsn doc.pending in
      match selected with
      | None -> None
      | Some selected ->
          let actual = TA.merge_into doc.actual selected in
          Some { doc with actual; pending }

  let with_actual doc f =
    let doc, act, res = f doc doc.actual in
    let doc = { doc with actual = act } in
    (doc, res)

  let next_p_ref doc =
    let next = doc.last_p_ref + 1 in
    ({ doc with last_p_ref = next }, next)
end

type tk = LspT.DocumentUri.t
type t = TD.t DocMap.t

let empty = DocMap.empty

(* Just record the text. It will be processed later, when a prover
   command or diagnostics query is issued by the client. *)
let add docs uri vsn txt =
  let tv = TV.make txt vsn in
  let upd = function
    | None -> Some (TD.make tv)
    | Some (doc : TD.t) -> Some (TD.add doc tv)
  in
  DocMap.update uri upd docs

let rem docs uri = DocMap.remove uri docs

let latest_vsn docs uri =
  match DocMap.find_opt uri docs with
  | None -> None
  | Some doc -> Some (TD.latest_vsn doc)

(* Here we merge pending versions with the actual and then run
   the supplied function on the prepared doc info. *)
let with_doc_vsn docs uri vsn f =
  match DocMap.find_opt uri docs with
  | None -> (docs, None)
  | Some doc -> (
      match TD.set_actual_vsn doc vsn with
      | None -> (docs, None)
      | Some doc ->
          let doc, res = TD.with_actual doc f in
          let docs = DocMap.add uri doc docs in
          (docs, res))

(* Push specific version to the actual, increase the proof_rec and clear the notifications. *)
let prepare_proof docs uri vsn range :
    t * (int * string * TlapmRange.t * ProofRes.t) option =
  with_doc_vsn docs uri vsn @@ fun (doc : TD.t) (act : TA.t) ->
  let next_doc, next_p_ref = TD.next_p_ref doc in
  match TA.prepare_proof act uri next_p_ref with
  | None -> (doc, act, None)
  | Some act ->
      let p_range = TA.locate_proof_range act range in
      let res = (next_p_ref, TA.text act, p_range, TA.proof_res act) in
      (next_doc, act, Some res)

(* Calculate proof range by user selection. *)
let suggest_proof_range docs uri range : t * (int * TlapmRange.t) option =
  match latest_vsn docs uri with
  | None -> (docs, None)
  | Some vsn ->
      with_doc_vsn docs uri vsn @@ fun (doc : TD.t) (act : TA.t) ->
      let p_range = TA.locate_proof_range act range in
      (doc, act, Some (vsn, p_range))

let add_obl docs uri vsn p_ref (obl : tlapm_obligation) =
  with_doc_vsn docs uri vsn @@ fun (doc : TD.t) (act : TA.t) ->
  match TA.add_obl act p_ref obl with
  | None -> (doc, act, None)
  | Some act -> (doc, act, Some (TA.proof_res act))

let add_notif docs uri vsn p_ref notif =
  with_doc_vsn docs uri vsn @@ fun (doc : TD.t) (act : TA.t) ->
  match TA.add_notif act p_ref notif with
  | None -> (doc, act, None)
  | Some act -> (doc, act, Some (TA.proof_res act))

let terminated docs uri vsn p_ref =
  with_doc_vsn docs uri vsn @@ fun (doc : TD.t) (act : TA.t) ->
  match TA.terminated act p_ref with
  | None -> (doc, act, None)
  | Some act -> (doc, act, Some (TA.proof_res act))

let get_proof_res docs uri vsn =
  with_doc_vsn docs uri vsn @@ fun doc act ->
  let act = TA.try_parse act uri in
  (doc, act, Some (TA.proof_res act))

let get_proof_res_latest docs uri =
  match latest_vsn docs uri with
  | None -> (docs, None, None)
  | Some latest_vsn ->
      let docs, res = get_proof_res docs uri latest_vsn in
      (docs, Some latest_vsn, res)

let get_obligation_state docs uri vsn range =
  with_doc_vsn docs uri vsn @@ fun doc act ->
  let act = TA.try_parse act uri in
  let res =
    match TA.get_obligation_state act range with
    | None -> None
    | Some ps -> PS.tlaps_proof_obligation_state_of_t uri ps
  in
  (doc, act, res)

let get_obligation_state_latest docs uri range =
  match latest_vsn docs uri with
  | None -> (docs, None)
  | Some latest_vsn ->
      let docs, res = get_obligation_state docs uri latest_vsn range in
      (docs, res)
