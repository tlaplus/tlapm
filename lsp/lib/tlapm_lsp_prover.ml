module Docs = Tlapm_lsp_docs

(* A megabyte is probably enough for tlapm IO. *)
let tlapm_buf_size = 1024 * 1024

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

type t = {
  sw : Eio.Switch.t;
  fs : Eio__.Fs.dir_ty Eio.Path.t;
  mgr : Eio_unix.Process.mgr_ty Eio.Process.mgr;
  docs : Docs.t;
  proc : [ `Generic | `Unix ] Eio.Process.ty Eio__.Std.r option;
}

(** Create instance of a prover process manager. *)
let create sw fs mgr docs = { sw; fs; mgr; docs; proc = None }

(** Cancel (all) the preceding prover instances. *)
let cancel_all st =
  match st.proc with
  | None -> st
  | Some proc ->
      Eio.Process.signal proc Sys.sigint;
      ignore (Eio.Process.await proc);
      { st with proc = None }

(* TODO: Implement. *)
let start_async'' st doc_uri _doc_vsn doc_text line_from line_till executable =
  let mod_path = Lsp.Types.DocumentUri.to_path doc_uri in
  let mod_dir =
    let open Eio.Path in
    st.fs / Filename.dirname mod_path
  in
  let mod_name = Filename.basename mod_path in
  let out_buf = Buffer.create tlapm_buf_size in
  let stdin = Eio.Flow.string_source doc_text in
  let stdout = Eio.Flow.buffer_sink out_buf in
  let proc_args =
    [
      "--toolbox";
      string_of_int line_from;
      string_of_int line_till;
      "--stdin";
      mod_name;
    ]
    (* TODO: Add support for the stdin option.  *)
  in
  let proc =
    Eio.Process.spawn st.mgr ~sw:st.sw ~executable ~cwd:mod_dir ~stdin ~stdout
      proc_args
  in
  Eio.Fiber.fork ~sw:st.sw (fun () -> (* TODO: .. *)
                                      ());
  { st with proc = Some proc }

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
            (start_async'' st' doc_uri doc_vsn doc_text line_from line_till
               executable)
      | None -> Error "Document not found")
  | Error reason -> Error reason

let start_async st doc_uri doc_vsn line_from line_till =
  start_async' st doc_uri doc_vsn line_from line_till

(* ********************** Test cases ********************** *)

let%test_unit "basics" =
  Eio_main.run @@ fun env ->
  Eio.Switch.run @@ fun sw ->
  let fs = Eio.Stdenv.fs env in
  let mgr = Eio.Stdenv.process_mgr env in
  let docs = Docs.empty in
  let du = Lsp.Types.DocumentUri.of_path "/tmp/any-file.tla" in
  let dv = 1 in
  let docs = Docs.add docs du dv "any\ncontent" in
  let pr = create sw fs mgr docs in
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
