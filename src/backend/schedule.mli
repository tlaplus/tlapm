(*
 * Copyright (C) 2012  Inria and Microsoft Corporation
 *)

(* A command is a shell command.  It is run with its stdin empty,
   its stdout and stderr redirected to the same pipe (which is sent
   to the PM's stdout).  The closing of this pipe indicates termination
   of the process. *)

(* After the delay is expired, the function [tc] is called,
   and it must tell what to do with the process: continue running it
   (with a new delay and a new [tc] function) or kill it. *)

(* When the process terminates or is killed, the function [dc]
   is called with the result of the process. Note that the exit code
   of the process is not recorded because it is  not reliable under
   Windows.  [dc] returns [true] for success (meaning that
   the other commands of the task will not be run. *)

(* Note that all delays are counted from the launch of the process. *)

type task = int * (unit -> computation) list

and computation =
  | Immediate of bool    (* already computed, argument is success *)
  | Todo of command      (* must launch process *)

and command = {
  line : string;         (* Shell command line *)
  timeout : float;       (* delay before running tc *)
  timec : timeout_cont;  (* function to launch after timeout *)
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

val run: int -> task list -> unit
(* [run max_threads tasks]
   Run the tasks described by [tasks], launching at most [max_threads]
   simultatenous processes.
 *)
