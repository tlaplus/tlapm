open Util
open Tlapm_lsp_prover
open Tlapm_lsp_prover.ToolboxProtocol

type t = {
  doc_vsn : Doc_vsn.t;
  p_ref : int;
  mule : (Tlapm_lib.Module.T.mule, unit) result option;
  nts : tlapm_notif list;  (** Parsing errors and warnings. *)
  ois : Obl_proofs.t OblMap.t;
      (** A set of obligation results.
          It is set to empty, if any tlapm_notif is received. *)
  pss : Proof_step.t list;
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

let vsn act = Doc_vsn.version act.doc_vsn
let text act = Doc_vsn.text act.doc_vsn

(** Merge new version of the text (Doc_vsn) into the existing actual version of the document. *)
let merge_into (act : t) (v : Doc_vsn.t) =
  let diff_pos = Doc_vsn.diff_pos act.doc_vsn v in
  let before_change = TlapmRange.before diff_pos in
  let ois =
    OblMap.filter
      (fun _ (oi : Obl_proofs.t) -> before_change (Obl_proofs.loc oi))
      act.ois
  in
  let nts =
    List.filter (fun (n : tlapm_notif) -> before_change n.loc) act.nts
  in
  { act with doc_vsn = v; mule = None; ois; nts; pss = [] }

let try_parse_anyway_locked uri (act : t) =
  let v = act.doc_vsn in
  match
    Tlapm_lib.module_of_string (Doc_vsn.text v) (LspT.DocumentUri.to_path uri)
  with
  | Ok mule ->
      let pss = Proof_step.of_module mule in
      let pss = Proof_step.with_tlapm_obligations pss act.ois in
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

let proof_res (act : t) : Doc_proof_res.t =
  let latest_obl (_, oi) = Obl_proofs.latest oi in
  let obs_list = List.map latest_obl (OblMap.to_list act.ois) in
  {
    p_ref = act.p_ref;
    obs = obs_list;
    nts = act.nts;
    pss = Proof_step.flatten act.pss;
  }

let prepare_proof (act : t) uri next_p_ref =
  let act = try_parse act uri in
  match act.mule with
  | None | Some (Error ()) -> None
  | Some (Ok _mule) -> Some { act with p_ref = next_p_ref; nts = [] }

let locate_proof_range act range = Proof_step.locate_proof_range act.pss range
let get_obligation_state act range = Proof_step.find_proof_step act.pss range

let add_obl (act : t) (p_ref : int) (obl : tlapm_obligation) =
  if act.p_ref = p_ref then
    let drop_older_intersecting (oRef : OblRef.t) (o : Obl_proofs.t) =
      oRef.p_ref = p_ref
      || not (TlapmRange.lines_intersect obl.loc (Obl_proofs.loc o))
    in
    let oi_ref = OblRef.make ~p_ref ~obl_id:obl.id in
    let oi =
      match OblMap.find_opt oi_ref act.ois with
      | None -> Obl_proofs.make obl
      | Some oi -> Obl_proofs.add_obl obl oi
    in
    let ois = OblMap.add oi_ref oi act.ois in
    let ois = OblMap.filter drop_older_intersecting ois in
    let pss = Proof_step.with_tlapm_obligation act.pss oi in
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
