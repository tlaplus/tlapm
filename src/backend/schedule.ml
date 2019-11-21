(*
 * Copyright (C) 2012  Inria and Microsoft Corporation
 *)

(* scheduler for back-end provers *)

Revision.f "$Rev$";;

open Unix;;

type task = int * (unit -> computation) list

and computation =
  | Immediate of bool    (* already computed, argument is success *)
  | Todo of command      (* must launch process *)

and command = {
  line : string;         (* shell command line *)
  timeout : float;       (* delay before running timec *)
  timec : timeout_cont;  (* function to call after timeout *)
  donec : result -> float -> bool;
    (* function to call when finished; float is time used; returns success *)
}

and timeout_cont = unit -> continue

and continue =
  | Timeout
  | Continue of timeout_cont * float

and result =
  | Finished
  | Stopped_kill
  | Stopped_timeout
;;

type process = {
  refid : int;
  pid : int;
  ofd : file_descr;
  start_time : float;
  dl : float;
  tc : timeout_cont;
  dc : result -> float -> bool;
  rest : (unit -> computation) list;
};;

let temp_buf = String.create 4096;;
let read_to_stdout fd =
  try
    let r = Unix.read fd temp_buf 0 (String.length temp_buf) in
    if r = 0 then raise End_of_file;
    output Pervasives.stdout temp_buf 0 r;
    flush Pervasives.stdout;
  with Unix_error _ -> raise End_of_file
;;

(* Take a computation, launch the process and return the corresponding
   [process] record. *)
let launch refid cmd t =
  System.harvest_zombies ();
  if !Params.verbose then begin
    Printf.eprintf "launching process: \"%s\"\n" cmd.line;
    flush Pervasives.stderr;
  end;
  let (pid, out_read) = System.launch_process cmd.line in
  let start_time = gettimeofday () in
  {
    refid = refid;
    pid = pid;
    ofd = out_read;
    start_time = start_time;
    dl = start_time +. cmd.timeout;
    tc = cmd.timec;
    dc = cmd.donec;
    rest = t;
  }
;;

(* Launch the first process of [comps], if any. *)
let rec start_process refid comps =
  match comps with
  | [] -> []
  | comp :: t ->
     begin match comp () with
     | Immediate false -> start_process refid t
     | Immediate true -> []
     | Todo cmd -> [launch refid cmd t]
     end
;;

(* Kill the process (or not, if reason = Finished) and return the success
   code from its "done" continuation. *)
let kill_process now reason d =
  if reason <> Finished then begin
    System.kill_tree d.pid;
  end;
  close d.ofd;
  d.dc reason (now -. d.start_time)
;;

let kill_and_start_next now reason d =
  let success = kill_process now reason d in
  if success then ([], []) else ([], [(d.refid, d.rest)])
;;

(* This function launches the proof tasks and calls their continuation
   functions when their deadlines expire and when they terminate.

   Note that this uses lists and is inefficient if there are
   many processes.  Optimize it if you have max_threads > 100.
*)
let run max_threads tl =
  assert (max_threads >= 1);
  assert (max_threads < 100);
  let rec spin running tl =
    let now = Unix.gettimeofday () in
    (* First check stdin for commands from the toolbox. *)
    (* "stop" command *)
    if Toolbox.is_stopped () then begin
      List.iter (fun d -> ignore (kill_process now Stopped_kill d)) running;
      raise Exit;
    end;
    (* toolbox "kill" command *)
    let kills = Toolbox.get_kills () in
    let f d =
      if List.mem d.refid kills then
        kill_and_start_next now Stopped_kill d
      else
        [d], []
    in
    let newruns, addtasks = List.split (List.map f running) in
    let running = List.flatten newruns in
    let tl = List.flatten addtasks @ tl in

    (* Then compute the next deadline. *)
    let dl = List.fold_left (fun x y -> min x y.dl) infinity running in
    if tl <> [] && List.length running < max_threads && now < dl then begin
      (* Then launch new tasks from the task list. This can take time, so
         do it only until the deadline is up. *)
      match tl with
      | [] -> assert false
      | (refid, comps) :: t -> spin (start_process refid comps @ running) t
    end else if running <> [] then begin
      (* Finally, call select and treat the outputs and deadlines. *)
      let outs = List.map (fun x -> x.ofd) running in
      let delay = max 0.0 (min (dl -. Unix.gettimeofday ()) 60.0) in
      let outs = if !Params.toolbox then Unix.stdin :: outs else outs in
      let (ready, _, _) = Unix.select outs [] [] delay in

      (* outputs *)
      let f d =
        if List.mem d.ofd ready then begin
          try
            read_to_stdout d.ofd;
            [d], []
          with End_of_file -> kill_and_start_next now Finished d
        end else
          [d], []
      in
      let newruns, addtasks = List.split (List.map f running) in
      let running = List.flatten newruns in
      let tl = List.flatten addtasks @ tl in

      (* deadlines *)
      let f d =
        if now >= d.dl then begin
          match d.tc () with
          | Timeout -> kill_and_start_next now Stopped_timeout d
          | Continue (tc, tmo) ->
             [ { d with tc = tc; dl = tmo +. d.start_time } ], []
        end else
          [d], []
      in
      let newruns, addtasks = List.split (List.map f running) in
      let running = List.flatten newruns in
      let tl = List.flatten addtasks @ tl in

      spin running tl;
    end (* else we are done. *)
  in
  try
    spin [] tl;
    System.harvest_zombies ();
  with Exit ->
    System.harvest_zombies ();
;;
