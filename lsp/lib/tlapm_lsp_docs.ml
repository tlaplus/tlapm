module Docs = Map.Make (Lsp.Types.DocumentUri)

type tv = { text : string; version : int; in_use : bool }
type td = { versions : tv list }
type tk = Lsp.Types.DocumentUri.t
type t = td Docs.t

let empty = Docs.empty

let add docs uri vsn txt =
  let rev = { text = txt; version = vsn; in_use = false } in
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
