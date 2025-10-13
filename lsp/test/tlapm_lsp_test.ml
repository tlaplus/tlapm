let () =
  let open Alcotest in
  run "tlapm_lsp"
    [
      ( "meta",
        [ test_case "Demo" `Quick (fun () -> Fmt.epr "XXX: It works!@.") ] );
    ]
