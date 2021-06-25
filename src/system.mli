(*
 * Copyright (C) 2012  INRIA and Microsoft Corporation
 *)

val kill_tree: int -> unit
(** [kill_tree pid]
    Kill the process tree rooted at [pid] (with signal 1).
*)

val harvest_zombies: unit -> unit
(** Use the wait system call to harvest the dead children processes. *)

val launch_process: string -> int * Unix.file_descr
(** [launch_process cmd]
    Launch a new process running shell command [cmd], return its PID
    and a file descriptor to its redirected standard and error outputs.
    Its standard input is closed.
*)

(*******************************************)

type line =
  | Line of string
  | Leof

type line_buffer;;

val make_line_buffer: Unix.file_descr -> line_buffer
(** [make_line_buffer fd]
    Allocate a line_buffer associated with file descriptor [fd] *)

val read_lines: line_buffer -> line list
(** [read_lines buf]
    Perform one [Unix.read] system call to fill the buffer [buf],
    and return the lines of characters read.  In case of an incomplete
    line, leave it in the buffer for the next call.  Append [Leof] to
    the list iff [Unix.read] returned an end of file.
*)

type toolbox_command =
  | Kill of int
  | Killall
  | Eof

val read_toolbox_commands:
    line_buffer -> toolbox_command list
(** [read_toolbox_commands buf]
    Use [read_lines] to get lines from [buf] and parse them as toolbox
    commands ("stop <n>" or "kill").
*)
