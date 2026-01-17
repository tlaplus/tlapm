module MultilineDiff : sig
  (** For comparing module texts showing multiline diff. *)

  include Alcotest.TESTABLE

  val same : t
  val diff : string -> string -> t
end = struct
  type t = Same | Differs of string

  let same = Same

  let diff a b =
    let open Patdiff in
    let prev = Diff_input.{ name = "a"; text = a } in
    let next = Diff_input.{ name = "b"; text = b } in
    let diff = Compare_core.diff_strings Configuration.default ~prev ~next in
    match diff with `Same -> Same | `Different s -> Differs s

  let pp fmt (t : t) =
    match t with
    | Same -> Fmt.string fmt "Same"
    | Differs d -> Fmt.pf fmt "Differs\n%s@." d

  let equal a b =
    match (a, b) with
    | Same, Same -> true
    | Same, Differs _ -> false
    | Differs _, Same -> false
    | Differs _, Differs _ -> failwith "cannot compare non empty diffs"
end

let check_multiline_diff ~title ~expected ~actual =
  Alcotest.check
    (module MultilineDiff)
    title MultilineDiff.same
    (MultilineDiff.diff expected actual)

let check_multiline_diff_td ~title ~expected ~actual =
  check_multiline_diff ~title ~expected ~actual:(Lsp.Text_document.text actual)

module CodeActionFound : sig
  (** Attempt to make test results a bit more understandable in the case of
      wrong code actions proposed. *)

  include Alcotest.TESTABLE

  val find :
    string ->
    [ `CodeAction of Lsp.Types.CodeAction.t | `Command of Lsp.Types.Command.t ]
    list ->
    t * t

  val get : t -> Lsp.Types.CodeAction.t
end = struct
  type t =
    | Found of Lsp.Types.CodeAction.t
    | NotFound of string * string list
    | Expected of string

  let pp fmt (t : t) =
    match t with
    | Found _ -> Fmt.string fmt "Found"
    | Expected pattern -> Fmt.pf fmt "Expected %s" pattern
    | NotFound (pattern, titles) ->
        Fmt.pf fmt "\nNotFound %s\nReceived:\n  %a" pattern
          (Fmt.list ~sep:Fmt.(const string "\n  ") Fmt.string)
          titles

  let equal a b =
    match (a, b) with Found _, _ | _, Found _ -> true | _ -> false

  let get a = match a with Found x -> x | _ -> assert false

  let strings_of_cas cas =
    cas
    |> List.map (fun x ->
        let open Lsp.Types in
        match x with
        | `Command ({ title; _ } : Command.t) -> Fmt.str "Command: %s" title
        | `CodeAction ({ title; _ } : CodeAction.t) ->
            Fmt.str "CodeAction: %s" title)

  let find pattern cas =
    let found =
      cas
      |> List.find_map (fun x ->
          let open Lsp.Types in
          match x with
          | `Command (_ : Command.t) -> None
          | `CodeAction (ca : CodeAction.t) ->
              if Str.string_match (Str.regexp pattern) ca.title 0 then Some ca
              else None)
    in
    let found =
      match found with
      | None -> NotFound (pattern, strings_of_cas cas)
      | Some ca -> Found ca
    in
    (found, Expected pattern)
end

let check_ca_proposed ~expected ~actual =
  Alcotest.check
    (module CodeActionFound)
    "Code Action should be proposed" expected actual

(** {1 Helpers for invoking LSP}*)

let lsp_init () =
  let lsp = Test_lsp_client.run "../bin/tlapm_lsp.exe" in
  let init_response = Test_lsp_client.call_init lsp in
  Alcotest.(
    check string "serverInfo.name" "tlapm-lsp"
      (init_response.serverInfo |> Option.get).name);
  Test_lsp_client.send_notification lsp Lsp.Client_notification.Initialized;
  lsp

let lsp_stop lsp = Test_lsp_client.close lsp

(** Invoke a Code Action at the specified line. *)
let lsp_ca ~lsp ?(name = "test") ~text ~line ca_regex =
  let path = Fmt.str "file:///tmp/%s.tla" name in
  let uri = Lsp.Uri.of_string path in

  let languageId = "tlaplus" in
  let did_open_doc_params =
    Lsp.Types.(
      DidOpenTextDocumentParams.create
        ~textDocument:
          (TextDocumentItem.create ~languageId ~text ~uri ~version:1))
  in
  Test_lsp_client.send_notification lsp
    (Lsp.Client_notification.TextDocumentDidOpen did_open_doc_params);

  let ca_response =
    let open Lsp.Types in
    Lsp.Client_request.CodeAction
      (CodeActionParams.create
         ~textDocument:(TextDocumentIdentifier.create ~uri)
         ~range:
           (Range.create
              ~start:(Position.create ~line ~character:0)
              ~end_:(Position.create ~line ~character:0))
         ~context:(CodeActionContext.create ~diagnostics:[] ())
         ())
    |> Test_lsp_client.call lsp |> CodeActionResult.t_of_yojson |> Option.get
  in
  let ca_expected =
    let found, expected = CodeActionFound.find ca_regex ca_response in
    check_ca_proposed ~expected ~actual:found;
    CodeActionFound.get found
  in
  let (actual : Lsp.Text_document.t) =
    let text_doc =
      Lsp.Text_document.make ~position_encoding:`UTF8 did_open_doc_params
    in
    Lsp.Text_document.apply_text_document_edits text_doc
      Lsp.Types.(
        ca_expected.edit |> Option.to_list
        |> List.map (fun (e : WorkspaceEdit.t) ->
            e.changes |> Option.get |> List.map snd |> List.flatten)
        |> List.flatten)
  in
  actual
