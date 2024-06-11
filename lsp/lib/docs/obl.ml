open Util
open Prover

module Role = struct
  type t =
    | Main  (** Main obligation for a proof step. *)
    | Aux  (** Auxiliary, created by the prover in the BY clause. *)
    | Unknown  (** Initially all the obligations are of unknown role. *)
    | Unexpected
        (** Was not received from the parser, but got later from the prover. *)

  let as_string = function
    | Main -> "main"
    | Aux -> "aux"
    | Unknown -> "unknown"
    | Unexpected -> "unexpected"
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
  checking : bool; (* Is obligation checking currently running? *)
  by_prover : Toolbox.Obligation.t StrMap.t;
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
    checking = false;
    by_prover = StrMap.empty;
    latest_prover = None;
    status;
  }

let with_role role obl = { obl with role }
let role obl = obl.role

(* Should exist in any case. *)
let loc obl =
  match obl.parsed with
  | None ->
      (match obl.latest_prover with
      | None ->
          assert false (* there should be either parsed info or prover result *)
      | Some prover -> StrMap.find prover obl.by_prover)
        .loc
  | Some parsed -> Range.of_locus_must (Tlapm_lib.Util.get_locus parsed.obl)

let fingerprint obl =
  match obl.parsed with None -> None | Some obl -> obl.fingerprint

let status obl = if obl.checking then Proof_status.Progress else obl.status

let is_final obl =
  match obl.latest_prover with
  | None -> None
  | Some prover ->
      let obl_state = StrMap.find prover obl.by_prover in
      Some (Toolbox.Obligation.is_final obl_state)

let text_plain obl = Lazy.force obl.parsed_text_plain
let text_normalized obl = Lazy.force obl.parsed_text_normalized

(** Try to get most detailed status message.
    Take it from the prover result, if exist. *)
let latest_status_msg obl =
  match obl.latest_prover with
  | None -> Proof_status.to_message obl.status
  | Some prover ->
      Toolbox.tlapm_obl_state_to_string
        (StrMap.find prover obl.by_prover).status

let latest_obl_text obl =
  match obl.latest_prover with
  | None -> text_normalized obl
  | Some prover -> (StrMap.find prover obl.by_prover).obl

let with_prover_terminated p_ref (obl : t) =
  if obl.p_ref <= p_ref then { obl with checking = false } else obl

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
          checking = false;
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
      checking = false;
      by_prover = StrMap.empty;
      latest_prover = None;
      status = Proof_status.Pending;
    }
  in
  let obl_add obl =
    let obl =
      { obl with checking = not (Toolbox.Obligation.is_final tlapm_obl) }
    in
    match Toolbox.Obligation.(tlapm_obl.prover) with
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
                checking = other.checking;
                by_prover = other.by_prover;
                latest_prover = other.latest_prover;
                status = other.status;
              }))
  | Some _ -> obl

let as_lsp_diagnostic (obl : t) =
  match Proof_status.is_diagnostic obl.status with
  | true ->
      let message = "Obligation: " ^ latest_status_msg obl in
      let message =
        match latest_obl_text obl with
        | None -> message
        | Some obl_text -> message ^ "\n" ^ obl_text
      in
      let severity = LspT.DiagnosticSeverity.Error in
      let range = Range.as_lsp_range (loc obl) in
      let source = Const.diagnostic_source in
      Some (LspT.Diagnostic.create ~message ~range ~severity ~source ())
  | false -> None

let as_lsp_tlaps_proof_obligation_state obl =
  let role = Role.as_string obl.role in
  let range = Range.as_lsp_range (loc obl) in
  let status = Proof_status.to_string obl.status in
  let normalized = text_normalized obl in
  let results =
    let open Toolbox.Obligation in
    let some_str s = match s with None -> "?" | Some s -> s in
    List.map
      (fun (_, o) ->
        let prover = some_str o.prover in
        let status =
          Proof_status.to_string (Proof_status.of_tlapm_obl_state o.status)
        in
        let meth = some_str o.meth in
        let reason = o.reason in
        let obligation = o.obl in
        Structs.TlapsProofObligationResult.make ~prover ~meth ~status ~reason
          ~obligation)
      (StrMap.to_list obl.by_prover)
  in
  Structs.TlapsProofObligationState.make ~role ~range ~status ~normalized
    ~results
