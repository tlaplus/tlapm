module DocMap = Map.Make (Lsp.Types.DocumentUri)
module OblMap = Map.Make (Int)
open Tlapm_lsp_prover.ToolboxProtocol

type tv = {
  text : string; (* Contents if the file at the specific version. *)
  version : int;
  in_use : bool;
  proof_ref : int; (* Increased with each launch of the prover. *)
  obligations : tlapm_obligation OblMap.t;
}

type td = { versions : tv list }
type tk = Lsp.Types.DocumentUri.t
type t = td DocMap.t

let empty = DocMap.empty

let add docs uri vsn txt =
  let rev =
    {
      text = txt;
      version = vsn;
      in_use = false;
      proof_ref = 0;
      obligations = OblMap.empty;
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

let get_vsn_opt docs uri vsn =
  match DocMap.find_opt uri docs with
  | None -> None
  | Some { versions } ->
      let matching v = if v.version = vsn then Some v.text else None in
      List.find_map matching versions

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

(* Increment the prover reference p_ref for the specified document / version. *)
let next_p_ref_opt (docs : td DocMap.t) uri vsn =
  match DocMap.find_opt uri docs with
  | None -> (docs, None)
  | Some { versions = [] } -> (docs, None)
  | Some { versions } ->
      let f acc v =
        match v with
        | { version = vv; proof_ref; text; _ } when vv = vsn ->
            let next_proof_ref = proof_ref + 1 in
            (Some (next_proof_ref, text), { v with proof_ref = next_proof_ref })
        | _ -> (acc, v)
      in
      let result, versions' = List.fold_left_map f None versions in
      let docs' =
        DocMap.update uri (fun _ -> Some { versions = versions' }) docs
      in
      (docs', result)
