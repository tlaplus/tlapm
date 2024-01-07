(* cSpell:words obligationsnumber getcwd nonblocking submatches *)

(* TODO: Use `opam exec -- tlapm --noproving --printallobs --toolbox 0 0 SetSum_proofs.tla`. *)

(** Max size for the read buffer, a line should fit into it.*)
let read_buf_max_size = 1024 * 1024

module TlapmRange = struct
  (* LSP ranges are 0-based and TLAPM is 1-based. In LSP the last char is exclusive. *)
  type t = R of (int * int) * (int * int)
  type p = P of int * int

  let line_from (R ((fl, _), _)) = fl
  let line_till (R (_, (tl, _))) = tl
  let from (R ((fl, fc), _)) = P (fl, fc)
  let till (R (_, (tl, tc))) = P (tl, tc)
  let p_add (P (l, c)) al ac = P (l + al, c + ac)

  let p_less (P (al, ac)) (P (bl, bc)) =
    match Stdlib.compare al bl with
    | 0 -> Stdlib.compare ac bc < 0
    | l_diff -> l_diff < 0

  let p_leq (P (al, ac)) (P (bl, bc)) =
    match Stdlib.compare al bl with
    | 0 -> Stdlib.compare ac bc <= 0
    | l_diff -> l_diff < 0

  let p_min a b = if p_less a b then a else b
  let p_max a b = if p_less a b then b else a

  let as_lsp_range (R ((fl, fc), (tl, tc))) =
    let open Lsp.Types in
    Range.create
      ~start:(Position.create ~line:(fl - 1) ~character:(fc - 1))
      ~end_:(Position.create ~line:(tl - 1) ~character:tc)

  let of_lsp_range (range : Lsp.Types.Range.t) =
    let f = (range.start.line + 1, range.start.character + 1) in
    let t = (range.end_.line + 1, range.end_.character) in
    R (f, t)

  let of_string_opt s =
    match String.split_on_char ':' s with
    | [ fl; fc; tl; tc ] ->
        let f = (int_of_string fl, int_of_string fc) in
        let t = (int_of_string tl, int_of_string tc - 1) in
        Some (R (f, t))
    | _ -> None

  let of_locus (locus : Tlapm_lib.Loc.locus) =
    match (locus.start, locus.stop) with
    | Actual start_pt, Actual stop_pt ->
        Some
          (R ((start_pt.line, start_pt.col), (stop_pt.line, stop_pt.col - 1)))
    | Dummy, _ | _, Dummy -> None

  let of_locus_opt (locus : Tlapm_lib.Loc.locus option) =
    match locus with None -> None | Some locus -> of_locus locus

  let of_lines fl tl = R ((fl, 1), (tl, 1))
  let of_points (P (fl, fc)) (P (tl, tc)) = R ((fl, fc), (tl, tc))

  let string_of_range (R ((fl, fc), (tl, tc))) : string =
    Format.sprintf "%d:%d:%d:%d" fl fc tl tc

  let string_of_pos (P (l, c)) = Format.sprintf "%d:%d" l c

  (* Where to show the location of error for which the location is unknown. *)
  let of_unknown = R ((1, 1), (1, 4))

  (* To pass it to TLAPM for checking all the document. *)
  let of_all = R ((0, 0), (0, 0))

  (** [before p r] means range [r] is before point [p]. *)
  let before p r = p_less (till r) p

  (* [intersect a b] is true, if ranges [a] and [b] overlaps. *)
  let intersect a b = p_leq (from a) (till b) && p_leq (from b) (till a)

  (* [lines_intersect a b] is true is line ranges for [a] and [b] intersect. *)
  let lines_intersect a b =
    let lfa = line_from a in
    let lta = line_till a in
    let lfb = line_from b in
    let ltb = line_till b in
    lfa <= ltb && lfb <= lta

  (* [lines_covered a b] is true if lines of [a] are fully covered by [b], i.e. [a] is inside of [b]. *)
  let lines_covered a b =
    let lfa = line_from a in
    let lta = line_till a in
    let lfb = line_from b in
    let ltb = line_till b in
    lfb <= lfa && lta <= ltb

  let lines_covered_or_all q rs =
    match List.filter (lines_intersect q) rs with
    | [] -> of_all
    | matching ->
        List.fold_left
          (fun acc m ->
            let from = p_min (from acc) (from m) in
            let till = p_max (till acc) (till m) in
            of_points from till)
          q matching

  let first_diff_pos a b =
    let len = min (String.length a) (String.length b) in
    let rec count i l c =
      if i = len then P (l, c)
      else
        let ai = String.get a i in
        let bi = String.get b i in
        if ai = bi then
          let l, c =
            match bi with '\n' -> (l + 1, 1) | '\r' -> (l, c) | _ -> (l, c + 1)
          in
          count (i + 1) l c
        else P (l, c)
    in
    count 0 1 1

  let%test_module "before" =
    (module struct
      let%test _ = not (before (P (3, 5)) (R ((1, 1), (5, 3))))
      let%test _ = not (before (P (3, 5)) (R ((1, 1), (3, 6))))
      let%test _ = not (before (P (3, 5)) (R ((1, 1), (3, 5))))
      let%test _ = before (P (3, 5)) (R ((1, 1), (2, 5)))
    end)

  let%test_module "first_diff_pos" =
    (module struct
      let%test "first" = P (1, 1) = first_diff_pos "hello" "bye"
      let%test "second" = P (1, 2) = first_diff_pos "hello" "hallo"
      let%test "next_ln" = P (2, 1) = first_diff_pos "sa\nme" "sa\ny"
      let%test "line_len_a" = P (1, 3) = first_diff_pos "same" "sa\n"
      let%test "line_len_b" = P (1, 3) = first_diff_pos "sa\n" "same"
      let%test "index_bounds_1" = P (1, 3) = first_diff_pos "mod" "mo"
      let%test "index_bounds_2" = P (1, 3) = first_diff_pos "mo" "mod"
    end)

  let%test_module "lines_covered_or_all" =
    (module struct
      let some = R ((10, 5), (11, 20))
      let before1 = R ((1, 1), (2, 10))
      let on_from = R ((9, 1), (10, 6))
      let on_till = R ((10, 20), (15, 8))
      let within = R ((10, 20), (11, 10))
      let%test _ = of_all = lines_covered_or_all some [ before1 ]
      let%test _ = some = lines_covered_or_all some [ within ]

      let%test _ =
        R ((9, 1), (15, 8)) = lines_covered_or_all some [ on_from; on_till ]
    end)
end

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

  (* NOTE: Strings don't have to match with the ones above. *)
  let tlapm_obl_state_to_string (s : tlapm_obl_state) : string =
    match s with
    | ToBeProved -> "to be proved"
    | BeingProved -> "being proved"
    | Normalized -> "normalized"
    | Proved -> "proved"
    | Failed -> "failed"
    | Interrupted -> "interrupted"
    | Trivial -> "trivial"
    | Unknown s -> "unknown state: " ^ s

  let tlapm_obl_state_is_terminal (s : tlapm_obl_state) : bool =
    match s with
    | ToBeProved -> false
    | BeingProved -> false
    | Normalized -> false
    | Proved -> true
    | Failed -> true
    | Interrupted -> false
    | Trivial -> true
    | Unknown _ -> false

  type tlapm_obligation = {
    id : int;
    loc : TlapmRange.t;
    status : tlapm_obl_state;
    fp : string option;
    prover : string option;
    meth : string option;
    reason : string option;
    already : bool option;
    obl : string option;
  }

  type tlapm_notif_severity = TlapmNotifError | TlapmNotifWarning

  type tlapm_notif = {
    loc : TlapmRange.t;
    sev : tlapm_notif_severity;
    msg : string;
    url : string option;
  }

  type tlapm_msg =
    | TlapmNotif of tlapm_notif
    | TlapmObligationsNumber of int
    | TlapmObligation of tlapm_obligation
    | TlapmTerminated

  type parser_part_msg =
    | PartWarning of { msg : string option }
    | PartError of { url : string option; msg : string option }
    | PartObligationsNumber of int option
    | PartObligation of {
        id : int option;
        loc : TlapmRange.t option;
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
    let re = Re2.create_exn {|^@!!([a-z]*):(.*)$|} in
    match Re2.find_submatches re line with
    | Ok [| _all_match; Some k; Some v |] -> Some (k, v)
    | Ok _ -> failwith "impossible"
    | Error _ -> None

  let rec guess_notif_loc' str = function
    | [] -> (TlapmRange.of_unknown, String.trim str)
    | `A :: others -> (
        let re =
          Re2.create_exn
            {|^File "(.*)", line ([0-9]+), character ([0-9]+) to line ([0-9]+), character ([0-9]+) :\n(.*)$|}
        in
        match Re2.find_submatches re str with
        | Ok
            [|
              _all_match;
              Some _File;
              Some line_from;
              Some char_from;
              Some line_till;
              Some char_till;
              Some rest_msg;
            |] ->
            ( TlapmRange.R
                ( (int_of_string line_from, int_of_string char_from),
                  (int_of_string line_till, int_of_string char_till) ),
              String.trim rest_msg )
        | Ok _ -> failwith "impossible"
        | Error _ -> guess_notif_loc' str others)
    | `B :: others -> (
        let re_opts = { Re2.Options.default with dot_nl = true } in
        let re =
          Re2.create_exn
            {|^File "(.*)", line ([0-9]+), characters ([0-9]+)-([0-9]+)\n(.*)|}
            ~options:re_opts
        in
        match Re2.find_submatches re str with
        | Ok
            [|
              _all_match;
              Some _file;
              Some line;
              Some char_from;
              Some char_till;
              Some rest_msg;
            |] ->
            ( TlapmRange.R
                ( (int_of_string line, int_of_string char_from),
                  (int_of_string line, int_of_string char_till) ),
              String.trim rest_msg )
        | Ok _ -> failwith "impossible"
        | Error _ -> guess_notif_loc' str others)
    | `C :: others -> (
        (* Messages like this: `File "aaa.tla", line 5, character 22` *)
        let re_opts = { Re2.Options.default with dot_nl = true } in
        let re =
          Re2.create_exn
            {|^File "(.*)", line ([0-9]+), character ([0-9]+)\n(.*)|}
            ~options:re_opts
        in
        match Re2.find_submatches re str with
        | Ok [| _all_match; Some _file; Some line; Some char; Some rest_msg |]
          ->
            ( TlapmRange.R
                ( (int_of_string line, int_of_string char),
                  (int_of_string line, int_of_string char + 4) ),
              String.trim rest_msg )
        | Ok _ -> failwith "impossible"
        | Error _ -> guess_notif_loc' str others)

  let guess_notif_loc str = guess_notif_loc' str [ `A; `B; `C ]

  let notif_of_loc_msg loc_opt msg =
    let sev = TlapmNotifWarning in
    let url = None in
    match loc_opt with
    | None -> { sev; loc = TlapmRange.of_unknown; msg; url }
    | Some loc_str ->
        let loc, _empty_msg = guess_notif_loc loc_str in
        { sev; loc; msg; url }

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
          | "loc" -> PartObligation { o with loc = TlapmRange.of_string_opt v }
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
      | PartWarning { msg = Some msg } ->
          let loc, msg = guess_notif_loc msg in
          Some (TlapmNotif { loc; sev = TlapmNotifWarning; msg; url = None })
      | PartWarning _ -> None
      | PartError { msg = Some msg; url } ->
          let loc, msg = guess_notif_loc msg in
          Some (TlapmNotif { loc; sev = TlapmNotifError; msg; url })
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
      let acc' = ToolboxProtocol.parse_line line acc stream in
      if Eio.Buf_read.at_end_of_input br then () else read_fun' br acc'
    in
    let read_fun br = read_fun' br ToolboxProtocol.parse_start in
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
      (* First arg s ignored, if executable is specified. *)
      executable;
      "--toolbox";
      string_of_int (TlapmRange.line_from range);
      string_of_int (TlapmRange.line_till range);
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

(* ********************** Test cases ********************** *)

let%test_unit "parse_line-obl-num" =
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

let%test_unit "parse-warning-loc" =
  let open ToolboxProtocol in
  let stream = Eio.Stream.create 10 in
  let stream_add = Eio.Stream.add stream in
  let expected_msg1 =
    "Warning: module name \"bbb\" does not match file name \"aaa.tla\"."
  in
  let expected_msg2 = "Operator \"prover\" not found" in
  let expected_msg3 = "Unexpected {" in
  let lines =
    [
      "@!!BEGIN";
      "@!!type:warning";
      "@!!msg:File \"aaa.tla\", line 1, character 1 to line 17, character 4 :";
      expected_msg1;
      "@!!END";
      "@!!BEGIN";
      "@!!type:warning";
      "@!!msg:File \"aaa.tla\", line 5, characters 9-14";
      "";
      expected_msg2;
      "";
      "@!!END";
      "@!!BEGIN";
      "@!!type:warning";
      "@!!msg:File \"aaa.tla\", line 5, character 22";
      expected_msg3;
      "@!!END";
    ]
  in
  match
    List.fold_left (fun acc l -> parse_line l acc stream_add) parse_start lines
  with
  | Empty -> (
      match Eio.Stream.length stream with
      | 3 -> (
          (match Eio.Stream.take stream with
          | TlapmNotif
              {
                msg;
                loc = R ((1, 1), (17, 4));
                sev = TlapmNotifWarning;
                url = None;
              }
            when msg = expected_msg1 ->
              ()
          | _ -> failwith "unexpected msg1");
          (match Eio.Stream.take stream with
          | TlapmNotif
              {
                msg;
                loc = R ((5, 9), (5, 14));
                sev = TlapmNotifWarning;
                url = None;
              }
            when msg = expected_msg2 ->
              ()
          | TlapmNotif { msg; loc; _ } ->
              failwith
                (Format.sprintf "msg=%S, loc=%s" msg
                   (TlapmRange.string_of_range loc))
          | _ -> failwith "unexpected msg2");
          match Eio.Stream.take stream with
          | TlapmNotif
              {
                msg;
                loc = R ((5, 22), (5, 26));
                sev = TlapmNotifWarning;
                url = None;
              }
            when msg = expected_msg3 ->
              ()
          | _ -> failwith "unexpected msg3")
      | _ -> failwith "unexpected msg count")
  | _ -> failwith "unexpected parser state"

let%test_module "Mocked TLAPM" =
  (module struct
    let test_case doc_name timeout assert_fun =
      Eio_main.run @@ fun env ->
      Eio.Switch.run @@ fun sw ->
      let fs = Eio.Stdenv.fs env in
      let mgr = Eio.Stdenv.process_mgr env in
      let du = Lsp.Types.DocumentUri.of_path doc_name in
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
          start_async pr du dv dt (TlapmRange.of_lines 3 7) events_adder
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
