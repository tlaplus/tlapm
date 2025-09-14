(*
 * toolbox.ml --- toolbox interaction
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Proof.T
open Expr.T
open Expr.Subst
open Property
open Method
open Types


let reason_to_string r =
  match r with
  | False -> "false"
  | Timeout -> "timeout"
  | Cantwork s -> s


let toolbox_print ob ?(temp=false) status prover meth timeout already print_ob
                  reason warnings time_used =
  if !Params.toolbox then begin
    let obl =
      match ob.kind with
      | Ob_error msg when print_ob ->
          Some (warnings ^ msg)
      | Ob_omitted _ -> None
      | _ when print_ob ->
          let buf = Buffer.create 100 in
          let ff = Format.formatter_of_buffer buf in
          if Params.debugging "trivial" && ob.kind = Ob_main then begin
            Format.fprintf ff "@[\\* not checked against known facts@]@."
          end;
          Format.fprintf ff "@[<b0>";
          ignore (Expr.Fmt.pp_print_sequent (Deque.empty, Ctx.dot) ff
                                            ~temp:temp ob.obl.core);
          Format.fprintf ff "@]@.";
          Some (warnings ^ Buffer.contents buf)
      | _ -> None
    in
    let times =
      if timeout = 0.
      then ""
      else begin
        match time_used with
        | None -> Printf.sprintf "time-limit: %g" timeout
        | Some tm ->
           Printf.sprintf "time-limit: %g; time-used: %.1f (%.0f%%)"
                          timeout tm (100. *. tm /. timeout)
      end
    in
    let meth_line =
      match meth, times with
      | None, "" -> None
      | None, _ -> Some times
      | Some m, "" -> Some m
      | Some m, _ -> Some (Printf.sprintf "%s; %s" m times)
    in
    Toolbox_msg.print_obligation
      ~id: (Option.get ob.Proof.T.id)
      ~loc: (Option.get (Util.query_locus ob.Proof.T.obl))
      ~status: status
      ~fp: (if !Params.fp_deb then ob.fingerprint else None)
      ~prover: prover
      ~meth: meth_line
      ~reason: (Option.map reason_to_string reason)
      ~already: already
      ~obl: obl
  end


let print_res_aux ob st fp do_print warns time_used =
  let status, prover, meth, timeout, print_ob, reason, temp =
    match st with
    | Triv ->
        "trivial", Some "tlapm", None, 0., !Params.printallobs, None, false
    | NTriv (r, m) ->
        let timeout = Method.timeout m in
        let temp = Method.is_temporal m in
        let p, s = prover_meth_of_tac m in
        begin match r with
        | RSucc -> "proved", p, s, timeout, !Params.printallobs, None, temp
        | RFail r -> "failed", p, s, timeout, do_print, r, temp
        | RInt -> "interrupted", p, s, timeout, do_print, None, temp
        end
  in
  toolbox_print ob ~temp status prover meth timeout fp print_ob reason warns
                time_used


let print_new_res ob st warns time_used =
  print_res_aux ob st (Some false) true warns time_used



(**** duplicates prep.ml *****)
let expand_defs ?(what = fun _ -> true) ob =
  let prefix = ref [] in
  let emit mu = prefix := mu :: (!prefix) in
  let rec visit sq =
    match Deque.front sq.context with
    | None -> sq
    | Some (h, hs) -> begin
        match h.core with
          | Defn ({core = Operator (_, e)}, wd, Visible, _) when what wd ->
              visit (app_sequent (scons e (shift 0)) { sq with context = hs })
          | _ ->
              emit h ;
              let sq = visit { sq with context = hs } in
                { sq with context = Deque.cons h sq.context }
      end
  in
  let obl = visit ob.obl.core in
     { ob with obl = { ob.obl with core = obl } }




let normalize really ob =
if not really then ob else
  let ob = expand_defs ob in
  match (Expr.Elab.normalize Deque.empty (noprops (Expr.T.Sequent ob.obl.core))).core with
    | Expr.T.Sequent sq ->
       { ob with obl = { ob.obl with core = sq } }
    | _ ->
        failwith "Toolbox.normalize.for.printing"


let print_old_res ob st really_print =
  if !Params.toolbox then
  let really_print = !Params.printallobs || really_print in
   print_res_aux (normalize really_print ob) st (Some true) really_print ""
                 None

(* FIXME obsolete these functions *)

let print_message msg =
  if !Params.toolbox then Toolbox_msg.print_warning msg


let print_message_url msg url =
  if !Params.toolbox then Toolbox_msg.print_error msg url


let print_ob_provers ob =
  if !Params.toolbox then
    let provers = Property.get ob.obl Proof.T.Props.meth in
    let provers = List.filter_map Method.prover_name_of_tac provers in
    let provers = List.unique provers in
    Toolbox_msg.print_obligationprovers (Option.get ob.id) provers

let print_ob_number n =
  if !Params.toolbox then Toolbox_msg.print_obligationsnumber n


(* --------------- *)

(* Functions to deal with toolbox commands ("stop" and "kill"). *)

let stopped = ref false
(* True iff the STOP command was found in stdin. *)

let killed = ref []
(* List of task ids found as argument of KILL command in stdin. *)

let got_eof = ref false
(* True iff an end-of-file was read on stdin. In that case, no further
   input will be read. *)

let line_buf = System.make_line_buffer Unix.stdin

(* Read standard input and update the [stopped] and [killed] variables. *)
let read_stdin () =
  if !Params.toolbox && not !got_eof then begin
    match Unix.select [Unix.stdin] [] [] 0.0 with
    | ([], _, _) -> ()
    | _ ->
       let cmds = System.read_toolbox_commands line_buf in
       let f cmd =
         match cmd with
         | System.Eof -> got_eof := true
         | System.Killall -> stopped := true
         | System.Kill id -> killed := id :: !killed
       in
       List.iter f cmds
  end


(* Get any pending commands from the toolbox and return true iff the toolbox
   sent "stop" at any point in the past. *)
let is_stopped () =
  read_stdin ();
  !stopped


(* Get any pending commands from the toolbox and return the list of new (since
   the last call to get_kills) task ids for which the toolbox sent the
   "kill <id>" command. *)
let get_kills () =
  read_stdin ();
  let result = !killed in
  killed := [];
  result
