let () =
    match Tlapm_lib.module_of_string "---- MODULE Test ---- x == 5 ====" with
    | None -> print_endline "Parse failed"
    | Some mule -> print_endline mule.core.name.core