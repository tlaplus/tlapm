open Tlapm_lib

let count_obls pred obls =
  Array.fold_left (fun acc obl -> acc + if pred obl then 1 else 0) 0 obls

let get_obls_stats (obls : Proof.T.obligation array) =
  let obl_cnt_pred kind = fun (obl : Proof.T.obligation) -> obl.kind = kind in
  let cnt_main = count_obls (obl_cnt_pred Proof.T.Ob_main) obls in
  let cnt_supp = count_obls (obl_cnt_pred Proof.T.Ob_support) obls in
  let cnt_expl =
    count_obls
      (fun (obl : Proof.T.obligation) -> Step_explainer.explain_obl obl != [])
      obls
  in
  let cnt_expl_main =
    count_obls
      (fun (obl : Proof.T.obligation) ->
        obl.kind = Ob_main && Step_explainer.explain_obl obl != [])
      obls
  in
  (Array.length obls, cnt_main, cnt_supp, cnt_expl, cnt_expl_main)

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

let collect_and_write oc filename =
  let all, main, supp, expl, expl_main = file_data_collector filename in
  Printf.fprintf oc "%s,%d,%d,%d,%d,%d\n"
    (Filename.basename filename)
    all main supp expl expl_main

let%test_unit "test obl runner" =
  let files_to_read = [] in
  let out_file = "./analysis/data.csv" in
  let oc = Out_channel.open_bin out_file in
  Printf.fprintf oc
    "Filename,All obligation count,Main obligation count,Support obligation \
     count,All explained obligation count,Main explained obligation count\n";
  List.iter (collect_and_write oc) files_to_read;
  close_out oc;
  assert true
