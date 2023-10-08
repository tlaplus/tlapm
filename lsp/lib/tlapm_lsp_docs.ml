module Docs = Map.Make (Lsp.Types.DocumentUri)

type tv = {
  text : string; (* Contents if the file at the specific version. *)
  version : int;
  in_use : bool;
  p_ref : int; (* Increased with each launch of the prover. *)
}

type td = { versions : tv list }
type tk = Lsp.Types.DocumentUri.t
type t = td Docs.t

let empty = Docs.empty

let add docs uri vsn txt =
  let rev = { text = txt; version = vsn; in_use = false; p_ref = 0 } in
  let drop_unused = List.filter (fun dd -> dd.in_use) in
  let upd = function
    | None -> Some { versions = [ rev ] }
    | Some d -> Some { versions = rev :: drop_unused d.versions }
  in
  Docs.update uri upd docs

let rem docs uri = Docs.remove uri docs

let get_opt docs uri =
  match Docs.find_opt uri docs with
  | None -> None
  | Some { versions = [] } -> None
  | Some { versions = v :: _ } -> Some (v.text, v.version)

let get_vsn_opt docs uri vsn =
  match Docs.find_opt uri docs with
  | None -> None
  | Some { versions } ->
      let matching v = if v.version = vsn then Some v.text else None in
      List.find_map matching versions

(* Increment the prover reference p_ref for the specified document / version. *)
let next_p_ref_opt (docs : td Docs.t) uri vsn =
  match Docs.find_opt uri docs with
  | None -> (docs, None)
  | Some { versions = [] } -> (docs, None)
  | Some { versions } ->
      let f acc v =
        match v with
        | { version = vv; p_ref; text; _ } when vv = vsn ->
            let next_p_ref = p_ref + 1 in
            (Some (next_p_ref, text), { v with p_ref = next_p_ref })
        | _ -> (acc, v)
      in
      let result, versions' = List.fold_left_map f None versions in
      let docs' =
        Docs.update uri (fun _ -> Some { versions = versions' }) docs
      in
      (docs', result)
