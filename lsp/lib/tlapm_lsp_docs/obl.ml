open Util
open Tlapm_lsp_prover.ToolboxProtocol

module Role = struct
  type t =
    | Main  (** Main obligation for a proof step. *)
    | Aux  (** Auxiliary, created by the prover in the BY clause. *)
    | Unknown  (** Initially all the obligations are of unknown role. *)
    | Unexpected
        (** Was not received from the parser, but got later from the prover. *)
end

type t = {
  role : Role.t;
  (* The obligation as received from the parser. *)
  parsed : Tlapm_lib.Proof.T.obligation option;
  (* The following work as a cache. *)
  parsed_text_plain : string option Lazy.t;
  parsed_text_normalized : string option Lazy.t;
  (* The following collect the proof info.
     For each new p_ref we reset all the prover results. *)
  p_ref : int;
  by_prover : tlapm_obligation StrMap.t;
  latest_prover : string option;
  status : Proof_status.t;
}

let obl_to_str obl =
  let buf = Buffer.create 100 in
  let fmt = Format.formatter_of_buffer buf in
  Tlapm_lib.Proof.Fmt.pp_print_obligation fmt obl;
  Format.pp_print_flush fmt ();
  Buffer.contents buf

let obl_to_normalized_str obl =
  obl_to_str (Tlapm_lib.Backend.Toolbox.normalize true obl)

let of_parsed_obligation parsed status =
  let parsed_text_plain = lazy (Option.map obl_to_str parsed) in
  let parsed_text_normalized = lazy (Option.map obl_to_normalized_str parsed) in
  {
    role = Role.Unknown;
    parsed;
    parsed_text_plain;
    parsed_text_normalized;
    p_ref = 0;
    by_prover = StrMap.empty;
    latest_prover = None;
    status;
  }

let with_role role obl = { obl with role }
let role obl = obl.role

(* Should exist in any case. *)
let loc obl =
  let open Tlapm_lsp_prover in
  match obl.parsed with
  | None ->
      (match obl.latest_prover with
      | None -> failwith "there should be either parsed info or prover result"
      | Some prover -> StrMap.find prover obl.by_prover)
        .loc
  | Some parsed ->
      TlapmRange.of_locus_must (Tlapm_lib.Util.get_locus parsed.obl)

let fingerprint obl =
  match obl.parsed with None -> None | Some obl -> obl.fingerprint

let status obl = obl.status
let text_plain obl = Lazy.force obl.parsed_text_plain
let text_normalized obl = Lazy.force obl.parsed_text_normalized

(** Try to get most detailed status message.
    Take it from the prover result, if exist. *)
let latest_status_msg obl =
  match obl.latest_prover with
  | None -> Proof_status.to_message obl.status
  | Some prover ->
      Tlapm_lsp_prover.ToolboxProtocol.tlapm_obl_state_to_string
        (StrMap.find prover obl.by_prover).status

let latest_obl_text obl =
  match obl.latest_prover with
  | None -> text_normalized obl
  | Some prover -> (StrMap.find prover obl.by_prover).obl

let with_prover_obligation p_ref tlapm_obl (obl : t option) =
  (* Create, if we had no such [Obl.t]. *)
  let obl =
    match obl with
    | None ->
        {
          role = Role.Unexpected;
          parsed = None;
          parsed_text_plain = lazy None;
          parsed_text_normalized = lazy None;
          p_ref = 0;
          by_prover = StrMap.empty;
          latest_prover = None;
          status = Proof_status.Pending;
        }
    | Some obl -> obl
  in
  let obl_reset obl =
    {
      obl with
      p_ref;
      by_prover = StrMap.empty;
      latest_prover = None;
      status = Proof_status.Pending;
    }
  in
  let obl_add obl =
    match tlapm_obl.prover with
    | None -> obl
    | Some prover ->
        {
          obl with
          by_prover = StrMap.add prover tlapm_obl obl.by_prover;
          latest_prover = Some prover;
          status = Proof_status.of_tlapm_obl_state tlapm_obl.status;
        }
  in
  (* Reset / update / ignore the prover info. *)
  if obl.p_ref < p_ref then obl_add (obl_reset obl)
  else if obl.p_ref = p_ref then obl_add obl
  else obl

let with_proof_state_from obl by_fp =
  match obl.latest_prover with
  | None -> (
      match fingerprint obl with
      | None -> obl
      | Some fp -> (
          match by_fp fp with
          | None -> obl
          | Some other ->
              {
                obl with
                p_ref = other.p_ref;
                status = other.status;
                by_prover = other.by_prover;
                latest_prover = other.latest_prover;
              }))
  | Some _ -> obl

let as_lsp_diagnostic (obl : t) =
  let open Tlapm_lsp_prover in
  match Proof_status.is_diagnostic obl.status with
  | true ->
      let message = "Obligation: " ^ latest_status_msg obl in
      let message =
        match latest_obl_text obl with
        | None -> message
        | Some obl_text -> message ^ "\n" ^ obl_text
      in
      let severity = LspT.DiagnosticSeverity.Error in
      let range = TlapmRange.as_lsp_range (loc obl) in
      let source = Const.diagnostic_source in
      Some (LspT.Diagnostic.create ~message ~range ~severity ~source ())
  | false -> None

let as_lsp_tlaps_proof_obligation_state obl =
  let open Tlapm_lsp_prover in
  let range = TlapmRange.as_lsp_range (loc obl) in
  let normalized = text_normalized obl in
  let results =
    let some_str s = match s with None -> "?" | Some s -> s in
    List.map
      (fun (_, o) ->
        let prover = some_str o.prover in
        let status =
          Proof_status.to_message (Proof_status.of_tlapm_obl_state o.status)
        in
        let meth = some_str o.meth in
        let reason = o.reason in
        let obligation = o.obl in
        Tlapm_lsp_structs.TlapsProofObligationResult.make ~prover ~meth ~status
          ~reason ~obligation)
      (StrMap.to_list obl.by_prover)
  in
  Tlapm_lsp_structs.TlapsProofObligationState.make ~range ~normalized ~results

(* TODO: That's a workaround for the progress calc. Should be removed later. *)
let is_state_terminal_in_p_ref p_ref obl =
  let is_term = Tlapm_lsp_prover.ToolboxProtocol.tlapm_obl_state_is_terminal in
  if obl.p_ref = p_ref then
    match obl.latest_prover with
    | None -> false
    | Some prover -> is_term (StrMap.find prover obl.by_prover).status
  else false
