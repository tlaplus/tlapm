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

  type parser_state =
    | Empty
    | Begin
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

  let match_line line =
    let re = Str.regexp "^@!!\\([a-z]*\\):\\(.*\\)$" in
    match Str.string_match re line 0 with
    | true ->
        let k = Str.matched_group 1 line in
        let v = Str.matched_group 2 line in
        Some (k, v)
    | false -> None

  let parse_start = Empty

  (* TODO: Handle multiline fields. *)
  let parse_line line acc stream =
    match (acc, line) with
    | Empty, "@!!BEGIN" -> Begin
    | Empty, _ -> Empty
    | Begin, "@!!type:warning" -> PartWarning { msg = None }
    | Begin, "@!!type:error" -> PartError { msg = None; url = None }
    | Begin, "@!!type:obligationsnumber" -> PartObligationsNumber None
    | Begin, "@!!type:obligation" ->
        PartObligation
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
          }
    | Begin, _ -> PartUnknown
    | PartWarning { msg = Some msg }, "@!!END" ->
        Eio.Stream.add stream (TlapmWarning { msg });
        Empty
    | PartWarning w, _ -> (
        match match_line line with
        | Some ("msg", v) -> PartWarning { msg = Some v }
        | Some (_, _) -> PartWarning w
        | None -> PartWarning w)
    | PartError { msg = Some msg; url = Some url }, "@!!END" ->
        Eio.Stream.add stream (TlapmError { msg; url });
        Empty
    | PartError e, _ -> (
        match match_line line with
        | Some ("msg", v) -> PartError { e with msg = Some v }
        | Some ("url", v) -> PartError { e with url = Some v }
        | Some (_, _) -> PartError e
        | None -> PartError e)
    | PartObligationsNumber (Some count), "@!!END" ->
        Eio.Stream.add stream (TlapmObligationsNumber count);
        Empty
    | PartObligationsNumber e, _ -> (
        match match_line line with
        | Some ("count", v) -> PartObligationsNumber (int_of_string_opt v)
        | Some (_, _) -> PartObligationsNumber e
        | None -> PartObligationsNumber e)
    | ( PartObligation
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
          },
        "@!!END" ) ->
        Eio.Stream.add stream
          (TlapmObligation
             { id; loc; status; fp; prover; meth; reason; already; obl });
        Empty
    | PartObligation o, _ -> (
        match match_line line with
        | Some ("id", v) -> PartObligation { o with id = int_of_string_opt v }
        | Some ("loc", v) ->
            PartObligation { o with loc = tlapm_loc_of_string_opt v }
        | Some ("status", v) ->
            PartObligation
              { o with status = Some (tlapm_obl_state_of_string v) }
        | Some ("fp", v) -> PartObligation { o with fp = Some v }
        | Some ("prover", v) -> PartObligation { o with prover = Some v }
        | Some ("meth", v) -> PartObligation { o with meth = Some v }
        | Some ("reason", v) -> PartObligation { o with reason = Some v }
        | Some ("already", v) ->
            PartObligation { o with already = bool_of_string_opt v }
        | Some ("obl", v) -> PartObligation { o with obl = Some v }
        | Some (_, _) -> PartObligation o
        | None -> PartObligation o)
    | _, "@!!END" -> Empty
    | _, _ -> acc
end

(* ***** Prover process management ****************************************** *)

(* Environment for the parser. Introduced mainly to make it testable. *)
module type ProverEnv = sig
  val tlapm_exe : unit -> (string, string) result
  val have_error : Lsp.Types.Range.t -> string -> unit
end

(** Default implementation for ProverEnv *)
module DefaultPE : ProverEnv = struct
  (*
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

  let have_error _r _m =
    (* TODO: Update the docs *)
    ()
end

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
  stream : ToolboxProtocol.tlapm_msg Eio.Stream.t;
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
    (* TODO: Add support for the stdin option.  *)
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
let start_async' st ?(pe = (module DefaultPE : ProverEnv)) doc_uri doc_vsn
    line_from line_till =
  let module PE = (val pe : ProverEnv) in
  match PE.tlapm_exe () with
  | Ok executable -> (
      match Docs.get_vsn_opt st.docs doc_uri doc_vsn with
      | Some doc_text ->
          let st' = cancel_all st in
          Ok
            (start_async_with_text st' doc_uri doc_vsn doc_text line_from
               line_till executable)
      | None -> Error "Document not found")
  | Error reason -> Error reason

(* The public version, just to avoid exposing the ProverEnv module type. *)
let start_async st doc_uri doc_vsn line_from line_till =
  start_async' st doc_uri doc_vsn line_from line_till

(* ********************** Test cases ********************** *)

let%test_unit "parse_line_warning" =
  let open ToolboxProtocol in
  let stream = Eio.Stream.create 10 in
  let lines =
    [ "@!!BEGIN"; "@!!type:obligationsnumber"; "@!!count:17"; "@!!END" ]
  in
  match
    List.fold_left (fun acc l -> parse_line l acc stream) parse_start lines
  with
  | Empty -> (
      match Eio.Stream.length stream with
      | 1 -> (
          match Eio.Stream.take stream with
          | TlapmObligationsNumber 17 -> ()
          | _ -> failwith "unexpected msg")
      | _ -> failwith "unexpected msg count")
  | _ -> failwith "unexpected parser state"

let%test_unit "basics" =
  Eio_main.run @@ fun env ->
  Eio.Switch.run @@ fun sw ->
  let fs = Eio.Stdenv.fs env in
  let mgr = Eio.Stdenv.process_mgr env in
  let docs = Docs.empty in
  let du = Lsp.Types.DocumentUri.of_path "TimingExit0.tla" in
  let dv = 1 in
  let docs = Docs.add docs du dv "any\ncontent" in
  let stream = Eio.Stream.create 10 in
  let pr = create sw fs mgr stream docs in
  let errs = ref [] in
  let pe =
    (module struct
      let tlapm_exe () =
        let cwd = Sys.getcwd () in
        Ok (Filename.concat cwd "../test/tlapm_mock.sh")

      let have_error _r m = errs := m :: !errs
    end : ProverEnv)
  in
  let _docs =
    match start_async' pr ~pe du dv 3 7 with
    | Ok docs -> docs
    | Error e -> failwith e
  in
  ()
