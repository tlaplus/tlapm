open Tlapm_lib

module Stringmap = Map.Make (struct
  type t = string

  let compare = String.compare
end)

type stats = {
  main : int;
  supp : int;
  expl_main : int;
  expl_supp : int;
  expl_counts_main : int Stringmap.t;
  expl_counts_supp : int Stringmap.t;
}

let map_to_string (map : int Stringmap.t) =
  Stringmap.to_seq map
  |> Seq.map (fun (key, value) -> Printf.sprintf "%s:%d" key value)
  |> Seq.fold_left
       (fun acc s -> if acc != "" then acc ^ ";" ^ s else acc ^ s)
       ""

let add_to_map map key =
  let current_count = Stringmap.find_opt key map |> Option.value ~default:0 in
  Stringmap.add key (current_count + 1) map

let update_string_cnt map expls =
  List.fold_left (fun map str -> add_to_map map str) map expls

let get_obls_stats (obls : Proof.T.obligation array) =
  let get_stats acc (obl : Proof.T.obligation) =
    let is_main = obl.kind = Proof.T.Ob_main in
    let is_supp = obl.kind = Proof.T.Ob_support in
    let expls = Step_explainer.explain_obl obl in
    let new_acc =
      {
        acc with
        main = (if is_main then acc.main + 1 else acc.main);
        supp = (if is_supp then acc.supp + 1 else acc.supp);
        expl_main =
          (if is_main && expls != [] then acc.expl_main + 1 else acc.expl_main);
        expl_supp =
          (if is_supp && expls != [] then acc.expl_supp + 1 else acc.expl_supp);
      }
    in
    let updated_expl_counts_main =
      if is_main then update_string_cnt new_acc.expl_counts_main expls
      else new_acc.expl_counts_main
    in
    let updated_expl_counts_supp =
      if is_supp then update_string_cnt new_acc.expl_counts_supp expls
      else new_acc.expl_counts_supp
    in
    {
      new_acc with
      expl_counts_main = updated_expl_counts_main;
      expl_counts_supp = updated_expl_counts_supp;
    }
  in
  let initial_stats =
    {
      main = 0;
      supp = 0;
      expl_main = 0;
      expl_supp = 0;
      expl_counts_main = Stringmap.empty;
      expl_counts_supp = Stringmap.empty;
    }
  in
  Array.fold_left (fun acc obl -> get_stats acc obl) initial_stats obls

let file_data_collector filename =
  let read_file file = In_channel.with_open_bin file In_channel.input_all in
  let content = read_file filename in
  let mule =
    Result.get_ok (Parser.module_of_string ~content ~filename ~loader_paths:[])
  in
  let final_obs =
    match mule.core.stage with
    | Module.T.Special | Module.T.Parsed | Module.T.Flat -> [||]
    | Module.T.Final { final_obs; _ } -> final_obs
  in
  get_obls_stats final_obs

let collect_and_write oc total i filename =
  Eio.traceln "Collecting file [%d/%d]: %s" (i + 1) total filename;
  let stats = file_data_collector filename in
  Printf.fprintf oc "%s,%d,%d,%d,%d,%d,%s,%s\n"
    (Filename.basename filename)
    (stats.main + stats.supp) stats.main stats.supp stats.expl_main
    stats.expl_supp
    (map_to_string stats.expl_counts_main)
    (map_to_string stats.expl_counts_supp)

let collect_stats_of_files input_files output_file =
  let files_total = List.length input_files in
  let oc = Out_channel.open_bin output_file in
  Printf.fprintf oc
    "File,All obs cnt,Main obs cnt,Supp obs cnt,Main expl obs cnt,Supp expl \
     obs cnt,Main details,Supp details\n";
  List.iteri (collect_and_write oc files_total) input_files;
  close_out oc

let%test_unit "collect files explanations stats" =
  let files_to_read = [] in
  let out_file = "./analysis/data.csv" in
  collect_stats_of_files files_to_read out_file;
  assert true
