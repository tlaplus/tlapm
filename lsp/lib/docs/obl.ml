open Util
open Prover

module Role = struct
  type t =
    | Main  (** Main obligation for a proof step. *)
    | Aux  (** Auxiliary, created by the prover in the BY clause. *)
    | Unknown  (** Initially all the obligations are of unknown role. *)
    | Unexpected
        (** Was not received from the parser, but got later from the prover. *)
  [@@deriving show]

  let as_string = function
    | Main -> "main"
    | Aux -> "aux"
    | Unknown -> "unknown"
    | Unexpected -> "unexpected"
end

(** We define obligation's map explicitly to have ability to print it. *)
module ObligationByProverMap = struct
  include StrMap

  type t = Toolbox.Obligation.t StrMap.t

  let pp ppf (m : t) =
    let it =
      iter
        (fun k v ->
          Format.fprintf ppf "@[%s -> %a;@]" k Toolbox.Obligation.pp v)
        m
    in
    it
end

type t = {
  parsed : Tlapm_lib.Proof.T.obligation option;
      [@printer fun _ fmt -> Printf.ifprintf fmt "...skipped..."]
      (** The obligation as received from the parser. *)
  parsed_text_plain : string option Lazy.t;  (** Works as a cache. *)
  parsed_text_normalized : string option Lazy.t;  (** Works as a cache. *)
  p_ref : int;
      (** We collect proof info in a scope of p_ref only. For each new p_ref we
          reset all the prover results. *)
  p_obl_id : int option;  (** Obligation ID, as assigned by the prover. *)
  checking : bool;  (** Is obligation checking currently running? *)
  by_prover : ObligationByProverMap.t;
  prover_names : string list option;
  latest_prover : string option;
  status : Proof_status.t;
}
[@@deriving show]

let obl_to_str obl =
  let buf = Buffer.create 100 in
  let fmt = Format.formatter_of_buffer buf in
  Tlapm_lib.Proof.Fmt.pp_print_obligation fmt obl;
  Format.pp_print_flush fmt ();
  Buffer.contents buf

let obl_to_normalized_str obl =
  obl_to_str (Tlapm_lib.Backend.Toolbox.normalize true obl)

let of_parsed_obligation (parsed : Tlapm_lib.Proof.T.obligation) =
  let parsed_text_plain = lazy (Some (obl_to_str parsed)) in
  let parsed_text_normalized = lazy (Some (obl_to_normalized_str parsed)) in
  {
    parsed = Some parsed;
    parsed_text_plain;
    parsed_text_normalized;
    p_ref = 0;
    p_obl_id = None;
    checking = false;
    by_prover = ObligationByProverMap.empty;
    prover_names = None;
    latest_prover = None;
    status = Pending;
  }

let reset obl p_ref =
  {
    obl with
    p_ref;
    p_obl_id = None;
    checking = false;
    by_prover = ObligationByProverMap.empty;
    prover_names = None;
    latest_prover = None;
    status = Proof_status.Pending;
  }

let role obl =
  match obl.parsed with
  | None -> Role.Unknown
  | Some o -> (
      match o.kind with
      | Tlapm_lib.Proof.T.Ob_main -> Role.Main
      | Tlapm_lib.Proof.T.Ob_support -> Role.Aux
      | Tlapm_lib.Proof.T.Ob_error _ -> Role.Unexpected)

(* Should exist in any case. *)
let loc obl =
  match obl.parsed with
  | None ->
      (match obl.latest_prover with
      | None ->
          assert false (* there should be either parsed info or prover result *)
      | Some prover -> ObligationByProverMap.find prover obl.by_prover)
        .loc
  | Some parsed -> Range.of_locus_must (Tlapm_lib.Util.get_locus parsed.obl)

let fingerprint obl =
  match obl.parsed with None -> None | Some obl -> obl.fingerprint

(** Check if this obligation has the specified id. *)
let is_for_obl_id obl p_ref obl_id =
  if p_ref = obl.p_ref then
    match obl.p_obl_id with None -> false | Some id -> id = obl_id
  else false

(** Either there exist a success result (the latest one), or we have outputs
    from all the provers. *)
let is_final obl =
  match obl.status with
  | Pending | Progress -> false
  | Proved | Omitted | Missing -> true
  | Failed -> (
      match obl.prover_names with
      | None -> false
      | Some prover_names ->
          let have_prover_result pn =
            ObligationByProverMap.mem pn obl.by_prover
          in
          List.for_all have_prover_result prover_names)

let status obl = if obl.checking then Proof_status.Progress else obl.status
let text_plain obl = Lazy.force obl.parsed_text_plain
let text_normalized obl = Lazy.force obl.parsed_text_normalized

(** Try to get most detailed status message. Take it from the prover result, if
    exist. *)
let latest_status_msg obl =
  match obl.latest_prover with
  | None -> Proof_status.to_message obl.status
  | Some prover ->
      Toolbox.tlapm_obl_state_to_string
        (ObligationByProverMap.find prover obl.by_prover).status

let latest_obl_text obl =
  match obl.latest_prover with
  | None -> text_normalized obl
  | Some prover -> (ObligationByProverMap.find prover obl.by_prover).obl

let with_prover_terminated p_ref (obl : t) =
  if obl.p_ref <= p_ref then { obl with checking = false } else obl

let with_prover_obligation p_ref (tlapm_obl : Toolbox.Obligation.t)
    (obl : t option) =
  (* Create, if we had no such [Obl.t]. *)
  let obl =
    match obl with
    | None ->
        {
          parsed = None;
          parsed_text_plain = lazy None;
          parsed_text_normalized = lazy None;
          p_ref = 0;
          (* To have it reset bellow. *)
          p_obl_id = None;
          checking = false;
          by_prover = ObligationByProverMap.empty;
          prover_names = None;
          latest_prover = None;
          status = Proof_status.Pending;
        }
    | Some obl -> obl
  in
  let obl_add obl =
    let obl =
      match Toolbox.Obligation.(tlapm_obl.prover) with
      | None -> obl
      | Some prover ->
          let latest_prover = Some prover in
          let by_prover =
            ObligationByProverMap.add prover tlapm_obl obl.by_prover
          in
          let status =
            ObligationByProverMap.fold
              (fun _ (o : Toolbox.Obligation.t) acc ->
                Proof_status.max (Proof_status.of_tlapm_obl_state o.status) acc)
              by_prover Pending
          in
          { obl with by_prover; latest_prover; status }
    in
    { obl with p_obl_id = Some tlapm_obl.id; checking = not (is_final obl) }
  in
  (* Reset / update / ignore the prover info. *)
  if obl.p_ref < p_ref then obl_add (reset obl p_ref)
  else if obl.p_ref = p_ref then obl_add obl
  else obl

let with_proof_state_from by_fp obl =
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
                p_obl_id = other.p_obl_id;
                checking = other.checking;
                by_prover = other.by_prover;
                prover_names = other.prover_names;
                latest_prover = other.latest_prover;
                status = other.status;
              }))
  | Some _ -> obl

let with_prover_names p_ref obl_id prover_names obl =
  let update obl =
    { obl with p_obl_id = Some obl_id; prover_names = Some prover_names }
  in
  (* Reset / update / ignore the prover info. *)
  if obl.p_ref < p_ref then update (reset obl p_ref)
  else if obl.p_ref = p_ref then update obl
  else obl

let as_lsp_diagnostic (obl : t) =
  match Proof_status.is_diagnostic obl.status with
  | true ->
      let message = "Obligation: " ^ latest_status_msg obl in
      let message =
        match latest_obl_text obl with
        | None -> message
        | Some obl_text -> message ^ "\n" ^ obl_text
      in
      let message = `String message in
      let severity = LspT.DiagnosticSeverity.Error in
      let range = Range.as_lsp_range (loc obl) in
      let source = Const.diagnostic_source in
      Some (LspT.Diagnostic.create ~message ~range ~severity ~source ())
  | false -> None

let as_lsp_tlaps_proof_obligation_state obl =
  let role = role obl |> Role.as_string in
  let range = Range.as_lsp_range (loc obl) in
  let status = Proof_status.to_string obl.status in
  let normalized = text_normalized obl in
  let results =
    let open Toolbox.Obligation in
    let some_str s = match s with None -> "?" | Some s -> s in
    let make_result o =
      let prover = some_str o.prover in
      let status =
        Proof_status.to_string (Proof_status.of_tlapm_obl_state o.status)
      in
      let meth = some_str o.meth in
      let reason = o.reason in
      let obligation = o.obl in
      Structs.TlapsProofObligationResult.make ~prover ~meth ~status ~reason
        ~obligation
    in
    let make_pending prover =
      Structs.TlapsProofObligationResult.make ~prover ~meth:(some_str None)
        ~status:(Proof_status.to_string Pending)
        ~reason:None ~obligation:None
    in
    (* Next, try to retain the order of the provers as it was reported
       by the tlaps. Only output pending/planned provers if the
       obligation state is not final yet. *)
    let final = is_final obl in
    match obl.prover_names with
    | None ->
        List.map
          (fun (_pn, o) -> make_result o)
          (ObligationByProverMap.to_list obl.by_prover)
    | Some prover_names ->
        let planned pn =
          match ObligationByProverMap.find_opt pn obl.by_prover with
          | None -> if final then None else Some (make_pending pn)
          | Some o -> Some (make_result o)
        in
        let unplanned (pn, o) =
          if List.mem pn prover_names then None else Some (make_result o)
        in
        List.append
          (List.filter_map planned prover_names)
          (List.filter_map unplanned
             (ObligationByProverMap.to_list obl.by_prover))
  in
  Structs.TlapsProofObligationState.make ~role ~range ~status ~normalized
    ~results

let%test_unit "Check Role.pp" =
  Format.printf "%a" Role.pp Role.Unexpected;
  assert ("Obl.Role.Unexpected" = Role.show Role.Unexpected)
