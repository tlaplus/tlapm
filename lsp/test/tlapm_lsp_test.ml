let init () =
  let lsp = Test_lsp_client.run "../bin/tlapm_lsp.exe" in
  let init_response = Test_lsp_client.call_init lsp in
  Alcotest.(
    check string "serverInfo.name" "tlapm-lsp"
      (init_response.serverInfo |> Option.get).name);
  Test_lsp_client.send_notification lsp Lsp.Client_notification.Initialized;
  lsp

let test_lsp_init () = init () |> Test_lsp_client.close

let test_lsp_decompose () =
  let lsp = init () in
  let name = "some" in
  let path = Fmt.str "file:///tmp/%s.tla" name in
  let uri = Lsp.Uri.of_string path in
  let text =
    {|
    ---- MODULE some ----
    THEOREM TestToSubSteps ==
        ASSUME NEW S PROVE \A a, b \in S : a
    PROOF
      <1>1. QED OBVIOUS
    ====
    |}
  in
  Test_lsp_client.send_notification lsp
    (Lsp.Client_notification.TextDocumentDidOpen
       { textDocument = { uri; version = 1; languageId = "tlaplus"; text } });

  let ca_response =
    let open Lsp.Types in
    Lsp.Client_request.CodeAction
      (CodeActionParams.create
         ~textDocument:(TextDocumentIdentifier.create ~uri)
         ~range:
           (Range.create
              ~start:(Position.create ~line:5 ~character:0)
              ~end_:(Position.create ~line:5 ~character:0))
         ~context:(CodeActionContext.create ~diagnostics:[] ())
         ())
    |> Test_lsp_client.call lsp |> CodeActionResult.t_of_yojson |> Option.get
  in
  (* TODO: Apply the code action. *)
  let _ca_to_sub_steps =
    ca_response
    |> List.find_map (fun x ->
           let open Lsp.Types in
           match x with
           | `Command (_ : Command.t) -> None
           | `CodeAction (ca : CodeAction.t) ->
               if ca.title = "⤮ To sub-steps" then Some ca else None)
    |> Option.get
  in
  Test_lsp_client.close lsp

let () =
  let open Alcotest in
  run "tlapm_lsp"
    [
      ( "meta",
        [
          test_case "Init" `Quick test_lsp_init;
          test_case "Decompose: to-steps" `Quick test_lsp_decompose;
        ] );
    ]
