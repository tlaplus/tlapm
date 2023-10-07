(* cSpell:words obligationsnumber Printexc sprintf getcwd nonblocking *)

module Docs = Tlapm_lsp_docs

(* ***** Types and parsers for them ***************************************** *)

module ToolboxProtocol = struct
  type tlapm_obl_state =
    | ToBeProved
    | BeingProved
    | Normalized
    | Proved
    | Failed
    | Interrupted
    | Trivial
    | Unknown of string

  let tlapm_obl_state_of_string s =
    match s with
    | "to be proved" -> ToBeProved
    | "being proved" -> BeingProved
    | "normalized" -> Normalized
    | "proved" -> Proved
    | "failed" -> Failed
    | "interrupted" -> Interrupted
    | "trivial" -> Trivial
    | _ -> Unknown s

  type tlapm_loc = (int * int) * (int * int)

  let range_of_loc (((fl, fc), (tl, tc)) : tlapm_loc) =
    let open Lsp.Types in
    Range.create
      ~start:(Position.create ~line:fl ~character:fc)
      ~end_:(Position.create ~line:tl ~character:tc)

  let tlapm_loc_of_string_opt s =
    match String.split_on_char ':' s with
    | [ fl; fc; tl; tc ] ->
        Some
          ( (int_of_string fl, int_of_string fc),
            (int_of_string tl, int_of_string tc) )
    | _ -> None

  type tlapm_msg =
    | TlapmWarning of { msg : string }
    | TlapmError of { url : string; msg : string }
    | TlapmObligationsNumber of int
    | TlapmObligation of {
        id : int;
        loc : tlapm_loc;
        status : tlapm_obl_state;
        fp : string option;
        prover : string option;
        meth : string option;
        reason : string option;
        already : bool option;
        obl : string option;
      }
    | TlapmTerminated

  type parser_part_msg =
    | PartWarning of { msg : string option }
    | PartError of { url : string option; msg : string option }
    | PartObligationsNumber of int option
    | PartObligation of {
        id : int option;
        loc : tlapm_loc option;
        status : tlapm_obl_state option;
        fp : string option;
        prover : string option;
        meth : string option;
        reason : string option;
        already : bool option;
        obl : string option;
      }
    | PartUnknown

  type parser_state =
    | Empty
    | Begin
    | PartMsg of {
        field : string option;
        acc_val : string;
        acc_msg : parser_part_msg;
      }

  let match_line line =
    let re = Str.regexp "^@!!\\([a-z]*\\):\\(.*\\)$" in
    match Str.string_match re line 0 with
    | true ->
        let k = Str.matched_group 1 line in
        let v = Str.matched_group 2 line in
        Some (k, v)
    | false -> None

  let parse_start = Empty

  let parse_line line acc stream =
    let new_msg m = PartMsg { field = None; acc_val = ""; acc_msg = m } in
    let set_field n v = function
      | PartWarning w -> (
          match n with
          | "msg" -> PartWarning { msg = Some v }
          | _ -> PartWarning w)
      | PartError e -> (
          match n with
          | "msg" -> PartError { e with msg = Some v }
          | "url" -> PartError { e with url = Some v }
          | _ -> PartError e)
      | PartObligationsNumber e -> (
          match n with
          | "count" -> PartObligationsNumber (int_of_string_opt v)
          | _ -> PartObligationsNumber e)
      | PartObligation o -> (
          match n with
          | "id" -> PartObligation { o with id = int_of_string_opt v }
          | "loc" -> PartObligation { o with loc = tlapm_loc_of_string_opt v }
          | "status" ->
              PartObligation
                { o with status = Some (tlapm_obl_state_of_string v) }
          | "fp" -> PartObligation { o with fp = Some v }
          | "prover" -> PartObligation { o with prover = Some v }
          | "meth" -> PartObligation { o with meth = Some v }
          | "reason" -> PartObligation { o with reason = Some v }
          | "already" ->
              PartObligation { o with already = bool_of_string_opt v }
          | "obl" -> PartObligation { o with obl = Some v }
          | _ -> PartObligation o)
      | PartUnknown -> PartUnknown
    in
    let msg_of_part = function
      | PartWarning { msg = Some msg } -> Some (TlapmWarning { msg })
      | PartWarning _ -> None
      | PartError { msg = Some msg; url = Some url } ->
          Some (TlapmError { msg; url })
      | PartError _ -> None
      | PartObligationsNumber (Some count) ->
          Some (TlapmObligationsNumber count)
      | PartObligationsNumber _ -> None
      | PartObligation
          {
            id = Some id;
            loc = Some loc;
            status = Some status;
            fp;
            prover;
            meth;
            reason;
            already;
            obl;
          } ->
          Some
            (TlapmObligation
               { id; loc; status; fp; prover; meth; reason; already; obl })
      | PartObligation _ -> None
      | PartUnknown -> None
    in
    match (acc, line) with
    | Empty, "@!!BEGIN" -> Begin
    | Empty, _ -> Empty
    | Begin, "@!!type:warning" -> new_msg (PartWarning { msg = None })
    | Begin, "@!!type:error" -> new_msg (PartError { msg = None; url = None })
    | Begin, "@!!type:obligationsnumber" -> new_msg (PartObligationsNumber None)
    | Begin, "@!!type:obligation" ->
        new_msg
          (PartObligation
             {
               id = None;
               loc = None;
               status = None;
               fp = None;
               prover = None;
               meth = None;
               reason = None;
               already = None;
               obl = None;
             })
    | Begin, _ -> new_msg PartUnknown
    | PartMsg { field; acc_val; acc_msg }, "@!!END" ->
        let maybe_out_msg =
          match field with
          | Some f -> msg_of_part (set_field f acc_val acc_msg)
          | None -> msg_of_part acc_msg
        in
        (match maybe_out_msg with Some out_msg -> stream out_msg | None -> ());
        Empty
    | (PartMsg { field; acc_val; acc_msg } as msg), _ -> (
        match match_line line with
        | Some (k, v) -> (
            match field with
            | Some f ->
                let acc_msg' = set_field f acc_val acc_msg in
                PartMsg { field = Some k; acc_val = v; acc_msg = acc_msg' }
            | None -> PartMsg { field = Some k; acc_val = v; acc_msg })
        | None -> (
            match field with
            | Some _ ->
                let acc_val' = acc_val ^ "\n" ^ line in
                PartMsg { field; acc_val = acc_val'; acc_msg }
            | None -> msg))
end

(* ***** Prover process management ****************************************** *)

(**
  Returns tha tlapm executable path or error, if there is no such in known places.
  If installed, both files are in the same dir:
    - .../bin/tlapm
    - .../bin/tlapm_lsp
  Otherwise, if that's development environment, the files are:
    - .../src/tlapm.exe
    - .../lsp/bin/tlapm_lsp.exe
  And during the inline tests:
    - .../src/tlapm.exe
    - .../lsp/lib/.tlapm_lsp_lib.inline-tests/inline_test_runner_tlapm_lsp_lib.exe
  *)
let tlapm_exe () =
  let open Filename in
  let this_exe = Sys.executable_name in
  let this_abs =
    match is_relative this_exe with
    | true -> concat current_dir_name this_exe
    | false -> this_exe
  in
  let tlapm_in_bin = concat (dirname this_abs) "tlapm" in
  let tlapm_in_src =
    let base_dir = dirname @@ dirname @@ dirname this_abs in
    concat (concat base_dir "src") "tlapm.exe"
  in
  let tlapm_in_tst =
    let base_dir = dirname @@ dirname @@ dirname @@ dirname this_abs in
    concat (concat base_dir "src") "tlapm.exe"
  in
  let paths_to_check = [ tlapm_in_bin; tlapm_in_src; tlapm_in_tst ] in
  match List.find_opt Sys.file_exists paths_to_check with
  | Some path -> Ok path
  | None ->
      Error
        ("tlapm not found, expected it among as: "
        ^ String.concat ", " paths_to_check)

(* Currently forked tlapm process. *)
type tf = {
  proc : [ `Generic | `Unix ] Eio.Process.ty Eio__.Std.r;
  complete : unit Eio.Promise.or_exn;
  cancel : unit Eio.Promise.u;
}

type t = {
  sw : Eio.Switch.t;
  fs : Eio__.Fs.dir_ty Eio.Path.t;
  mgr : Eio_unix.Process.mgr_ty Eio.Process.mgr;
  stream : ToolboxProtocol.tlapm_msg -> unit;
  docs : Docs.t;
  forked : tf option;
}

(** Create instance of a prover process manager. *)
let create sw fs mgr stream docs = { sw; fs; mgr; stream; docs; forked = None }

(** Cancel (all) the preceding prover instances. *)
let cancel_all st =
  match st.forked with
  | None -> st
  | Some { proc; complete; cancel } ->
      Eio.Process.signal proc Sys.sigkill;
      (match Eio.Process.await proc with
      | `Exited x -> Eio.traceln "[TLAPM] Process exited %d" x
      | `Signaled x ->
          Eio.traceln "[TLAPM] Process signalled %d" x;
          Eio.Promise.resolve cancel ());
      (match Eio.Promise.await complete with
      | Ok () -> Eio.traceln "[TLAPM] Fiber exited"
      | Error e ->
          Eio.traceln "[TLAPM] Fiber failed with %s" (Printexc.to_string e));
      { st with forked = None }

(* Start a fiber to read the tlapm stdout asynchronously. *)
let fork_read sw stream r w cancel =
  let fib_read () =
    Eio.Flow.close w;
    let rec read_fun' br acc =
      let line = Eio.Buf_read.line br in
      let acc' = ToolboxProtocol.parse_line line acc stream in
      if Eio.Buf_read.at_end_of_input br then () else read_fun' br acc'
    in
    let read_fun br = read_fun' br ToolboxProtocol.parse_start in
    let read_result =
      Eio.Buf_read.parse ~initial_size:5 ~max_size:200 read_fun r
    in
    (match read_result with
    | Ok () -> Eio.traceln "TLAPM process completed."
    | Error (`Msg msg) -> Eio.traceln "TLAPM process failed with: %s" msg);
    Eio.Flow.close r;
    Eio.traceln "TLAPM read fiber completed."
  in
  let fib_cancel () = Eio.Promise.await cancel in
  Eio.Fiber.fork_promise ~sw @@ fun () ->
  Eio.Fiber.first fib_read fib_cancel;
  stream TlapmTerminated;
  Eio.traceln "TLAPM main fiber completed"

(** Start the TLAPM process and attach the reader fiber to it. *)
let start_async_with_text st doc_uri _doc_vsn doc_text line_from line_till
    executable =
  let mod_path = Lsp.Types.DocumentUri.to_path doc_uri in
  let mod_dir =
    let open Eio.Path in
    st.fs / Filename.dirname mod_path
  in
  let mod_name = Filename.basename mod_path in
  let stdin = Eio.Flow.string_source doc_text in
  let r, w = Eio.Process.pipe st.mgr ~sw:st.sw in
  let proc_args =
    [
      (* First arg s ignored, id executable is specified. *)
      "tlapm";
      "--toolbox";
      string_of_int line_from;
      string_of_int line_till;
      "--stdin";
      mod_name;
    ]
  in
  let proc =
    Eio.Process.spawn st.mgr ~sw:st.sw ~executable ~cwd:mod_dir ~stdin ~stdout:w
      proc_args
  in
  let cancel_p, cancel_r = Eio.Promise.create () in
  let complete = fork_read st.sw st.stream r w cancel_p in
  let forked = { proc; complete; cancel = cancel_r } in
  { st with forked = Some forked }

(* Run the tlapm prover, cancel the preceding one, if any. *)
let start_async st doc_uri doc_vsn line_from line_till
    ?(tlapm_locator = tlapm_exe) () =
  match tlapm_locator () with
  | Ok executable -> (
      match Docs.get_vsn_opt st.docs doc_uri doc_vsn with
      | Some doc_text ->
          let st' = cancel_all st in
          Ok
            (start_async_with_text st' doc_uri doc_vsn doc_text line_from
               line_till executable)
      | None -> Error "Document not found")
  | Error reason -> Error reason

(* ********************** Test cases ********************** *)

let%test_unit "parse_line-warning" =
  let open ToolboxProtocol in
  let stream = Eio.Stream.create 10 in
  let stream_add = Eio.Stream.add stream in
  let lines =
    [
      (* keep it multiline*)
      "@!!BEGIN";
      "@!!type:obligationsnumber";
      "@!!count:17";
      "@!!END";
    ]
  in
  match
    List.fold_left (fun acc l -> parse_line l acc stream_add) parse_start lines
  with
  | Empty -> (
      match Eio.Stream.length stream with
      | 1 -> (
          match Eio.Stream.take stream with
          | TlapmObligationsNumber 17 -> ()
          | _ -> failwith "unexpected msg")
      | _ -> failwith "unexpected msg count")
  | _ -> failwith "unexpected parser state"

let%test_unit "parse_line-multiline" =
  let open ToolboxProtocol in
  let stream = Eio.Stream.create 10 in
  let stream_add = Eio.Stream.add stream in
  let lines =
    [
      "@!!BEGIN";
      "@!!type:obligation";
      "@!!id:2";
      "@!!loc:10:3:10:10";
      "@!!status:failed";
      "@!!prover:isabelle";
      "@!!meth:auto; time-limit: 30; time-used: 0.0 (0%)";
      "@!!reason:false";
      "@!!already:false";
      "@!!obl:";
      "ASSUME NEW CONSTANT A";
      "PROVE  \\A x \\in A : A \\in x";
      "";
      "@!!END";
    ]
  in
  match
    List.fold_left (fun acc l -> parse_line l acc stream_add) parse_start lines
  with
  | Empty -> (
      match Eio.Stream.length stream with
      | 1 -> (
          let obl =
            "\nASSUME NEW CONSTANT A\nPROVE  \\A x \\in A : A \\in x\n"
          in
          match Eio.Stream.take stream with
          | TlapmObligation { obl = Some o; _ } when o = obl -> ()
          | TlapmObligation { obl = Some o; _ } ->
              failwith (Format.sprintf "unexpected: %s" o)
          | _ -> failwith "unexpected msg")
      | _ -> failwith "unexpected msg count")
  | _ -> failwith "unexpected parser state"

let%test_module "Mocked TLAPM" =
  (module struct
    let test_case doc_name timeout assert_fun =
      Eio_main.run @@ fun env ->
      Eio.Switch.run @@ fun sw ->
      let fs = Eio.Stdenv.fs env in
      let mgr = Eio.Stdenv.process_mgr env in
      let docs = Docs.empty in
      let du = Lsp.Types.DocumentUri.of_path doc_name in
      let dv = 1 in
      let docs = Docs.add docs du dv "any\ncontent" in
      let stream = Eio.Stream.create 10 in
      let stream_add = Eio.Stream.add stream in
      let pr = create sw fs mgr stream_add docs in
      let tlapm_locator () =
        let cwd = Sys.getcwd () in
        Ok (Filename.concat cwd "../test/tlapm_mock.sh")
      in
      let clock = Eio.Stdenv.clock env in
      let ts_start = Eio.Time.now clock in
      let pr =
        match start_async pr du dv 3 7 ~tlapm_locator () with
        | Ok pr -> pr
        | Error e -> failwith e
      in
      let _pr = assert_fun pr clock stream in
      let ts_end = Eio.Time.now clock in
      let () =
        match ts_end -. ts_start < timeout with
        | true -> ()
        | false -> failwith "timeout expired"
      in
      ()

    (* Check a document which outputs a warning then sleeps for 3s and then
       outputs another. We will cancel it in 0.5s, only the first warning
       should be received, and the overall time should be less than a second. *)
    let%test_unit "Mocked: CancelTiming" =
      test_case "CancelTiming.tla" 1.0 @@ fun pr clock stream ->
      let () = Eio.Time.sleep clock 0.5 in
      let _pr = cancel_all pr in
      let () =
        match Eio.Stream.length stream with
        | 2 -> ()
        | l -> failwith (Format.sprintf "expected 2 events, got %d" l)
      in
      let () =
        match Eio.Stream.take_nonblocking stream with
        | Some (TlapmWarning { msg = "message before delay" }) -> ()
        | _ -> failwith "expected warning msg"
      in
      let () =
        match Eio.Stream.take_nonblocking stream with
        | Some TlapmTerminated -> ()
        | _ -> failwith "expected termination msg"
      in
      pr

    (* Check if abnormal tlapm termination don't cause any side effects.
       We con't sleep or cancel a process here, just wait for expected messages. *)
    let%test_unit "Mocked: AbnormalExit" =
      test_case "AbnormalExit.tla" 1.0 @@ fun pr _clock stream ->
      let () =
        match Eio.Stream.take stream with
        | TlapmWarning { msg = "this run is going to fail" } -> ()
        | _ -> failwith "expected warning msg"
      in
      let () =
        match Eio.Stream.take stream with
        | TlapmTerminated -> ()
        | _ -> failwith "expected termination msg"
      in
      pr

    (* Check if output of running tlapm on a document with no proofs works. *)
    let%test_unit "Mocked: Empty" =
      test_case "Empty.tla" 1.0 @@ fun pr _clock stream ->
      let () =
        match Eio.Stream.take stream with
        | TlapmObligationsNumber 0 -> ()
        | _ -> failwith "expected 0 obligations"
      in
      let () =
        match Eio.Stream.take stream with
        | TlapmTerminated -> ()
        | _ -> failwith "expected termination msg"
      in
      pr

    (* Check if output of running tlapm on a document with some proofs works. *)
    let%test_unit "Mocked: Some" =
      test_case "Some.tla" 1.0 @@ fun pr _clock stream ->
      let () =
        match Eio.Stream.take stream with
        | TlapmObligation { status = ToBeProved; _ } -> ()
        | _ -> failwith "expected obligation"
      in
      let () =
        match Eio.Stream.take stream with
        | TlapmObligationsNumber 1 -> ()
        | _ -> failwith "expected 1 obligations"
      in
      let () =
        match Eio.Stream.take stream with
        | TlapmObligation { status = Proved; _ } -> ()
        | _ -> failwith "expected obligation"
      in
      let () =
        match Eio.Stream.take stream with
        | TlapmTerminated -> ()
        | _ -> failwith "expected termination msg"
      in
      pr
  end)
