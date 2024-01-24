(* cSpell:words obligationsnumber getcwd nonblocking submatches *)

(* TODO: Use `opam exec -- tlapm --noproving --printallobs --toolbox 0 0 SetSum_proofs.tla`. *)

(** Max size for the read buffer, a line should fit into it.*)
let read_buf_max_size = 1024 * 1024

module LspT = Lsp.Types
module Progress = Progress
module Toolbox = Toolbox

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
  forked : tf option;
}

(** Create instance of a prover process manager. *)
let create sw fs mgr = { sw; fs; mgr; forked = None }

(** Cancel (all) the preceding prover instances. *)
let cancel_all st =
  match st.forked with
  | None -> st
  | Some { proc; complete; cancel; _ } ->
      Eio.Process.signal proc Sys.sigint;
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
      Eio.traceln "[TLAPM][O] %s" line;
      let acc' = Toolbox.parse_line line acc stream in
      if Eio.Buf_read.at_end_of_input br then () else read_fun' br acc'
    in
    let read_fun br = read_fun' br Toolbox.parse_start in
    let read_result =
      Eio.Buf_read.parse ~initial_size:5 ~max_size:read_buf_max_size read_fun r
    in
    (match read_result with
    | Ok () -> Eio.traceln "[TLAPM] process completed."
    | Error (`Msg msg) -> Eio.traceln "[TLAPM] process failed with: %s" msg);
    Eio.Flow.close r;
    Eio.traceln "[TLAPM] read fiber completed."
  in
  let fib_cancel () = Eio.Promise.await cancel in
  Eio.Fiber.fork_promise ~sw @@ fun () ->
  Eio.Fiber.first fib_read fib_cancel;
  stream TlapmTerminated;
  Eio.traceln "[TLAPM] main fiber completed"

(** Start the TLAPM process and attach the reader fiber to it. *)
let start_async_with_exec st doc_uri _doc_vsn doc_text range events_adder
    executable =
  let mod_path = LspT.DocumentUri.to_path doc_uri in
  let mod_dir =
    let open Eio.Path in
    st.fs / Filename.dirname mod_path
  in
  let mod_name = Filename.basename mod_path in
  let stdin = Eio.Flow.string_source doc_text in
  let r, w = Eio.Process.pipe st.mgr ~sw:st.sw in
  let proc_args =
    [
      (* First arg s ignored, if executable is specified. *)
      executable;
      "--toolbox";
      string_of_int (Range.line_from range);
      string_of_int (Range.line_till range);
      (* "--verbose"; *)
      "--printallobs";
      "--stdin";
      mod_name;
    ]
  in
  Eio.traceln "[TLAPM] cwd=%s, command: %s"
    (Eio.Path.native_exn mod_dir)
    (String.concat " " proc_args);
  let proc =
    Eio.Process.spawn st.mgr ~sw:st.sw ~executable ~cwd:mod_dir ~stdin ~stdout:w
      ~stderr:w proc_args
  in
  let cancel_p, cancel_r = Eio.Promise.create () in
  let complete = fork_read st.sw events_adder r w cancel_p in
  let forked = { proc; complete; cancel = cancel_r } in
  { st with forked = Some forked }

(* Run the tlapm prover, cancel the preceding one, if any. *)
let start_async st doc_uri doc_vsn doc_text range events_adder
    ?(tlapm_locator = tlapm_exe) () =
  Eio.traceln "[TLAPM][I]\n%s" doc_text;
  match tlapm_locator () with
  | Ok executable ->
      let st' = cancel_all st in
      Ok
        (start_async_with_exec st' doc_uri doc_vsn doc_text range events_adder
           executable)
  | Error reason -> Error reason

let%test_module "Mocked TLAPM" =
  (module struct
    let test_case doc_name timeout assert_fun =
      Eio_main.run @@ fun env ->
      Eio.Switch.run @@ fun sw ->
      let fs = Eio.Stdenv.fs env in
      let mgr = Eio.Stdenv.process_mgr env in
      let du = LspT.DocumentUri.of_path doc_name in
      let dv = 1 in
      let dt = "any\ncontent" in
      let events = Eio.Stream.create 10 in
      let events_adder = Eio.Stream.add events in
      let pr = create sw fs mgr in
      let tlapm_locator () =
        let cwd = Sys.getcwd () in
        Ok (Filename.concat cwd "../test/tlapm_mock.sh")
      in
      let clock = Eio.Stdenv.clock env in
      let ts_start = Eio.Time.now clock in
      let pr =
        match
          start_async pr du dv dt (Range.of_lines 3 7) events_adder
            ~tlapm_locator ()
        with
        | Ok pr -> pr
        | Error e -> failwith e
      in
      let _pr = assert_fun pr clock events in
      let ts_end = Eio.Time.now clock in
      let () =
        match ts_end -. ts_start < timeout with
        | true -> ()
        | false ->
            failwith
              (Format.sprintf "timeout %f expired in %f" timeout
                 (ts_end -. ts_start))
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
        | Some (TlapmNotif { msg = "message before delay"; _ }) -> ()
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
        | TlapmNotif { msg = "this run is going to fail"; _ } -> ()
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

    (* Check if STDIN is passed properly to the TLAPM process. *)
    let%test_unit "Mocked: Echo" =
      test_case "Echo.tla" 1.0 @@ fun pr _clock stream ->
      let () =
        match Eio.Stream.take stream with
        | TlapmNotif { msg; _ } -> (
            match msg with
            | "any\ncontent" -> ()
            | _ -> failwith (Format.sprintf "unexpected msg=%S" msg))
        | _ -> failwith "expected obligation"
      in
      pr
  end)
