module OblRef = struct
  type t = int * int

  let compare (p_ref_a, obl_id_a) (p_ref_b, obl_id_b) =
    let p_ref_cmp = Stdlib.compare p_ref_a p_ref_b in
    if p_ref_cmp = 0 then Stdlib.compare obl_id_a obl_id_b else p_ref_cmp
end

module DocMap = Map.Make (Lsp.Types.DocumentUri)
module OblMap = Map.Make (OblRef)
open Tlapm_lsp_prover
open Tlapm_lsp_prover.ToolboxProtocol

type tv = {
  text : string; (* Contents if the file at the specific version. *)
  version : int;
  in_use : bool; (* TODO: Is it needed? *)
  p_ref : int;
  (* Increased with each launch of the prover. *)
  (* TODO: Change to a list of ongoing proofs. *)
  nts : tlapm_notif list;
  obs : tlapm_obligation OblMap.t;
}

type td = { versions : tv list }
type tk = Lsp.Types.DocumentUri.t
type t = td DocMap.t
type proof_res = (tlapm_obligation list * tlapm_notif list) option option

let empty = DocMap.empty

let add docs uri vsn txt =
  (* TODO: Inherit and/or cleanup the obligations/warnings. *)
  let rev =
    {
      text = txt;
      version = vsn;
      in_use = false;
      p_ref = 0;
      nts = [];
      obs = OblMap.empty;
    }
  in
  let drop_unused = List.filter (fun dd -> dd.in_use) in
  let upd = function
    | None -> Some { versions = [ rev ] }
    | Some d -> Some { versions = rev :: drop_unused d.versions }
  in
  DocMap.update uri upd docs

let rem docs uri = DocMap.remove uri docs

let get_opt docs uri =
  match DocMap.find_opt uri docs with
  | None -> None
  | Some { versions = [] } -> None
  | Some { versions = v :: _ } -> Some (v.text, v.version)

let with_doc_vsn docs uri vsn f =
  match DocMap.find_opt uri docs with
  | None -> (None, docs)
  | Some { versions } ->
      let update acc v =
        if v.version = vsn then
          let v', ret = f v in
          (Some ret, v')
        else (acc, v)
      in
      let res, versions' = List.fold_left_map update None versions in
      let docs' = DocMap.add uri { versions = versions' } docs in
      (res, docs')

let prepare_proof docs uri vsn =
  with_doc_vsn docs uri vsn @@ fun v ->
  let v = { v with p_ref = v.p_ref + 1; nts = [] } in
  let obs_list = List.map snd (OblMap.to_list v.obs) in
  (v, (v.p_ref, v.text, Some (Some (obs_list, v.nts))))

let add_obl docs uri vsn p_ref (obl : tlapm_obligation) =
  with_doc_vsn docs uri vsn @@ fun v ->
  if v.p_ref = p_ref then
    let drop_older_intersecting (o_pr, _o_id) (o : tlapm_obligation) =
      o_pr = p_ref || not (TlapmRange.intersects obl.loc o.loc)
    in
    let obs = OblMap.add (p_ref, obl.id) obl v.obs in
    let obs = OblMap.filter drop_older_intersecting obs in
    let obs_list = List.map snd (OblMap.to_list obs) in
    ({ v with obs }, Some (obs_list, v.nts))
  else (v, None)

let add_notif docs uri vsn p_ref notif =
  with_doc_vsn docs uri vsn @@ fun v ->
  if v.p_ref = p_ref then
    let nts = notif :: v.nts in
    let obs_list = List.map snd (OblMap.to_list v.obs) in
    ({ v with nts }, Some (obs_list, nts))
  else (v, None)

let get_proof_res docs uri vsn =
  with_doc_vsn docs uri vsn @@ fun v ->
  (* TODO: Update the proof state if missing. Then return it.
      - Clean obl/err markers starting at the first changed line.
      - Update derived obl markers based on the parser's output.
  *)
  (v, None)
