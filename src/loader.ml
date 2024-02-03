module StrMap = Map.Make (String)

type zip_path = {
  zip_file : Zip.in_file Lazy.t;  (** The jar/zip file. *)
  entry_path : string -> string;
      (** Function to obtain a path of a module within the zip file. *)
}

type t = {
  zips : zip_path list;  (** All the zip files specified as paths. *)
  dirs : string list;  (** All the folders specified as paths. *)
  mods : string StrMap.t;
      (** Maps mod_name to file_content.
          A list of files specified explicitly. *)
}

let rec drop_prefix prefixes path =
  match prefixes with
  | [] -> None
  | prefix :: prefixes -> (
      match String.starts_with ~prefix path with
      | true ->
          let p_len = String.length prefix in
          let path = String.sub path p_len (String.length path - p_len) in
          Some path
      | false -> drop_prefix prefixes path)

let drop_prefix_if_any prefixes path =
  Option.value ~default:path (drop_prefix prefixes path)

let make paths =
  let partition path (zips, dirs) =
    match drop_prefix [ "jar:"; "zip:" ] path with
    | Some path ->
        let zip_path, entry_path =
          match String.split_on_char '!' path with
          | [ path ] -> (path, fun p -> p)
          | [ file_part; entry_part ] -> (
              let file_part = drop_prefix_if_any [ "file:" ] file_part in
              let entry_part = drop_prefix_if_any [ "/" ] entry_part in
              match entry_part with
              | "" -> (file_part, fun m -> m)
              | _ -> (file_part, fun m -> String.concat "/" [ entry_part; m ]))
          | _ -> failwith (Format.sprintf "unexpected path format: %s" path)
        in
        let zip_file = lazy (Zip.open_in zip_path) in
        let zip_path = { zip_file; entry_path } in
        (zip_path :: zips, dirs)
    | None -> (zips, path :: dirs)
  in
  let zips, dirs = List.fold_right partition paths ([], []) in
  { zips; dirs; mods = StrMap.empty }

let close t =
  List.iter
    (fun zip_path ->
      match Lazy.is_val zip_path.zip_file with
      | true -> Zip.close_in (Lazy.force zip_path.zip_file)
      | false -> ())
    t.zips;
  { t with zips = [] }

let with_dir t dir_name =
  match List.mem dir_name t.dirs with
  | true -> t
  | false -> { t with dirs = dir_name :: t.dirs }

let with_module t mod_name content =
  let mods = StrMap.add mod_name content t.mods in
  { t with mods }

let rec load_from_zips t mod_name =
  let check zip =
    let zip_file = Lazy.force zip.zip_file in
    match Zip.find_entry zip_file (zip.entry_path mod_name) with
    | zip_entry -> Some (Zip.read_entry zip_file zip_entry)
    | exception Not_found -> None
  in
  List.find_map check t.zips

let load_from_dirs t mod_name =
  let check dir =
    let path = Filename.concat dir mod_name in
    match Sys.file_exists path with
    | true ->
        let ic = open_in path in
        let content = In_channel.input_all ic in
        let () = close_in ic in
        Some content
    | false -> None
  in
  match List.find_map check t.dirs with
  | None -> load_from_zips t mod_name
  | Some content -> Some content

let load_from_mods t mod_name =
  match StrMap.find_opt mod_name t.mods with
  | None -> load_from_dirs t mod_name
  | Some content -> Some content

let load t mod_name = load_from_mods t mod_name

module Global = struct
  let loader : t option ref = ref None

  let close () =
    match !loader with None -> () | Some l -> loader := Some (close l)

  let reset () =
    close ();
    loader := None

  let setup paths =
    close ();
    loader := Some (make paths)

  let add_module mod_name content =
    loader := Some (with_module (Option.get !loader) mod_name content)

  let load mod_name = load (Option.get !loader) mod_name
end
