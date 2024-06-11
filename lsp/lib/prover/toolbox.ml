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

(* The strings here don't have to match with the ones above. *)
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

module Obligation = struct
  type t = {
    id : int;
    loc : Range.t;
    status : tlapm_obl_state;
    fp : string option;
    prover : string option;
    meth : string option;
    reason : string option;
    already : bool option;
    obl : string option;
  }

  (** Indicates if we should not expect any other obligation messages with the same id. *)
  let is_final o =
    match o.status with
    | ToBeProved -> false
    | BeingProved -> false
    | Normalized -> false
    | Proved -> true
    | Failed -> ( match o.prover with Some "isabelle" -> true | _ -> false)
    | Interrupted -> true
    | Trivial -> true
    | Unknown _ -> false

  (** This is for testing only. *)
  module Test = struct
    let with_id_status id status =
      {
        id;
        loc = Range.of_unknown;
        status;
        fp = None;
        prover = None;
        meth = None;
        reason = None;
        already = None;
        obl = None;
      }
  end
end

type tlapm_notif_severity = TlapmNotifError | TlapmNotifWarning

type tlapm_notif = {
  loc : Range.t;
  sev : tlapm_notif_severity;
  msg : string;
  url : string option;
}

module Msg = struct
  type t =
    | TlapmNotif of tlapm_notif
    | TlapmObligationsNumber of int
    | TlapmObligation of Obligation.t
    | TlapmTerminated
end

type parser_part_msg =
  | PartWarning of { msg : string option }
  | PartError of { url : string option; msg : string option }
  | PartObligationsNumber of int option
  | PartObligation of {
      id : int option;
      loc : Range.t option;
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
  | Ok _ -> assert false
  | Error _ -> None

let rec guess_notif_loc' str = function
  | [] -> (Range.of_unknown, String.trim str)
  | `A :: others -> (
      let re =
        Re2.create_exn
          {|^File "(.*)", line ([0-9]+), character ([0-9]+) to line ([0-9]+), character ([0-9]+) :\n?(.*)$|}
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
          ( Range.of_ints ~lf:(int_of_string line_from)
              ~cf:(int_of_string char_from) ~lt:(int_of_string line_till)
              ~ct:(int_of_string char_till),
            String.trim rest_msg )
      | Ok _ -> assert false
      | Error _ -> guess_notif_loc' str others)
  | `B :: others -> (
      let re_opts = { Re2.Options.default with dot_nl = true } in
      let re =
        Re2.create_exn
          {|^File "(.*)", line ([0-9]+), characters ([0-9]+)-([0-9]+)\n?(.*)|}
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
          ( Range.of_ints ~lf:(int_of_string line) ~cf:(int_of_string char_from)
              ~lt:(int_of_string line) ~ct:(int_of_string char_till),
            String.trim rest_msg )
      | Ok _ -> failwith "impossible"
      | Error _ -> guess_notif_loc' str others)
  | `C :: others -> (
      (* Messages like this: `File "aaa.tla", line 5, character 22` *)
      let re_opts = { Re2.Options.default with dot_nl = true } in
      let re =
        Re2.create_exn
          {|^File "(.*)", line ([0-9]+), character ([0-9]+)\n?(.*)|}
          ~options:re_opts
      in
      match Re2.find_submatches re str with
      | Ok [| _all_match; Some _file; Some line; Some char; Some rest_msg |] ->
          ( Range.of_ints ~lf:(int_of_string line) ~cf:(int_of_string char)
              ~lt:(int_of_string line)
              ~ct:(int_of_string char + 4),
            String.trim rest_msg )
      | Ok _ -> assert false
      | Error _ -> guess_notif_loc' str others)

let guess_notif_loc str = guess_notif_loc' str [ `A; `B; `C ]

let notif_of_loc_msg loc_opt msg =
  let sev = TlapmNotifWarning in
  let url = None in
  match loc_opt with
  | None -> { sev; loc = Range.of_unknown; msg; url }
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
        | "loc" -> PartObligation { o with loc = Range.of_string_opt v }
        | "status" ->
            PartObligation
              { o with status = Some (tlapm_obl_state_of_string v) }
        | "fp" -> PartObligation { o with fp = Some v }
        | "prover" -> PartObligation { o with prover = Some v }
        | "meth" -> PartObligation { o with meth = Some v }
        | "reason" -> PartObligation { o with reason = Some v }
        | "already" -> PartObligation { o with already = bool_of_string_opt v }
        | "obl" -> PartObligation { o with obl = Some v }
        | _ -> PartObligation o)
    | PartUnknown -> PartUnknown
  in
  let msg_of_part = function
    | PartWarning { msg = Some msg } ->
        let loc, msg = guess_notif_loc msg in
        Some (Msg.TlapmNotif { loc; sev = TlapmNotifWarning; msg; url = None })
    | PartWarning _ -> None
    | PartError { msg = Some msg; url } ->
        let loc, msg = guess_notif_loc msg in
        Some (Msg.TlapmNotif { loc; sev = TlapmNotifError; msg; url })
    | PartError _ -> None
    | PartObligationsNumber (Some count) -> Some (TlapmObligationsNumber count)
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

(* ********************** Test cases ********************** *)

let%test_unit "parse_line-obl-num" =
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
          let expected_loc1 = Range.of_ints ~lf:1 ~cf:1 ~lt:17 ~ct:4 in
          let expected_loc2 = Range.of_ints ~lf:5 ~cf:9 ~lt:5 ~ct:14 in
          let expected_loc3 = Range.of_ints ~lf:5 ~cf:22 ~lt:5 ~ct:26 in
          (match Eio.Stream.take stream with
          | TlapmNotif { msg; loc; sev = TlapmNotifWarning; url = None }
            when msg = expected_msg1 && loc = expected_loc1 ->
              ()
          | _ -> failwith "unexpected msg1");
          (match Eio.Stream.take stream with
          | TlapmNotif { msg; loc; sev = TlapmNotifWarning; url = None }
            when msg = expected_msg2 && loc = expected_loc2 ->
              ()
          | TlapmNotif { msg; loc; _ } ->
              failwith
                (Format.sprintf "msg=%S, loc=%s" msg
                   (Range.string_of_range loc))
          | _ -> failwith "unexpected msg2");
          match Eio.Stream.take stream with
          | TlapmNotif { msg; loc; sev = TlapmNotifWarning; url = None }
            when msg = expected_msg3 && loc = expected_loc3 ->
              ()
          | _ -> failwith "unexpected msg3")
      | _ -> failwith "unexpected msg count")
  | _ -> failwith "unexpected parser state"
