open Test_utils

let test_lsp_init () = lsp_init () |> lsp_stop

let () =
  let open Alcotest in
  run "tlapm_lsp"
    [
      ("meta", [ test_case "Init" `Quick test_lsp_init ]);
      ("decompose", Test_decompose.test_cases);
    ]
