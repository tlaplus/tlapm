(*
 * Copyright (C) 2012  INRIA and Microsoft Corporation
 *)

(** A few system-related functions *)


(* Kill the process tree rooted at the given PID.  This is done by
   parsing the output of "ps x" (or "ps -l").  We don't use process
   groups because they don't seem to be available on Cygwin.
*)

module Intmap = Map.Make (struct type t = int let compare = compare end)

let win_kill pid =
  ignore (Sys.command (Printf.sprintf "taskkill /PID %d /F" pid))


let unix_kill pid =
  try Unix.kill pid 1 with _ -> ()


let ps_list = [
  "cygwin", "ps -l", format_of_string " PID PPID PGID WINPID",
    format_of_string "%_c %d %d %_d %d", win_kill;

  "unix", "ps x -o pid,ppid,pid", format_of_string " PID PPID PID",
    format_of_string" %d %d %d", unix_kill;
]

let (_, ps_cmd, _, ps_format, kill_fn) =
  let test (_, cmd, hd, _, _) =
    let psout = Unix.open_process_in cmd in
    let l = input_line psout in
    let result =
      try Scanf.sscanf l hd (); true
      with Scanf.Scan_failure _ -> false
    in
    ignore (Unix.close_process_in psout);
    result
  in
  List.find test ps_list


let kill_tree pid =
  try
    let scanline l = Scanf.sscanf l ps_format (fun x y z -> (x, y, z)) in
    let psout = Unix.open_process_in ps_cmd in
    let _ = input_line psout in
    let rec mktree tree map =
      match (try Some (input_line psout) with End_of_file -> None) with
      | None -> (tree, map)
      | Some l ->
         let (pid, ppid, kpid) = scanline l in
         let sons = try Intmap.find ppid tree with Not_found -> [] in
         let newtree = Intmap.add ppid (pid :: sons) tree in
         let newmap = Intmap.add pid kpid map in
         mktree newtree newmap
    in
    let (t, m) = mktree Intmap.empty Intmap.empty in
    ignore (Unix.close_process_in psout);
    let rec kill pid =
      let kpid = Intmap.find pid m in
      kill_fn kpid;
      let sons = try Intmap.find pid t with Not_found -> [] in
      List.iter kill sons;
    in
    kill pid;
  with _ -> ()


(* Use the wait system call to harvest the dead children processes. *)
let harvest_zombies () =
  let rec spin () =
    let (pid, _) = Unix.waitpid [Unix.WNOHANG] (-1) in
    if pid <> 0 then spin ();
  in
  try spin () with Unix.Unix_error _ -> ()


let launch_process cmd =
  let (out_read, out_write) = Unix.pipe () in
  let (in_read, in_write) = Unix.pipe () in
  let pid = Unix.create_process "/bin/sh" [| "/bin/sh"; "-c"; cmd |]
                                in_read out_write out_write
  in
  Unix.close out_write;
  Unix.close in_read;
  Unix.close in_write;
  (pid, out_read)


(*****************************************)

type line =
  | Line of string
  | Leof


type line_buffer = {
  desc : Unix.file_descr;
  buf : Buffer.t;
}

let make_line_buffer fd = {desc = fd; buf = Buffer.create 100}

let rawbuf = Bytes.create 1000

let read_lines buf =
  let n = Unix.read buf.desc rawbuf 0 (Bytes.length rawbuf) in
  if n = 0 then begin
    let last = Buffer.contents buf.buf in
    Buffer.reset buf.buf;
    if last = "" then [Leof] else [Line last; Leof]
  end else begin
    Buffer.add_subbytes buf.buf rawbuf 0 n;
    let data = Buffer.contents buf.buf in
    let lines = Ext.split data '\n' in
    match List.rev lines with
    | [] -> assert false;
    | last :: rest ->
       Buffer.clear buf.buf;
       Buffer.add_string buf.buf last;
       List.map (fun x -> Line (x ^ "\n")) (List.rev rest)
  end


type toolbox_command =
  | Kill of int
  | Killall
  | Eof


let parse_command l =
  match l with
  | Line line ->
     if Ext.is_prefix "stop" line then
       try Scanf.sscanf line "stop %d" (fun id -> [Kill id]) with _ -> []
     else if Ext.is_prefix "kill" line then
       [Killall]
     else
       []  (* ignore unknown input *)
  | Leof -> [Eof]


let read_toolbox_commands buf =
  List.flatten (List.map parse_command (read_lines buf))
