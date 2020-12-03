(*
 * Copyright (C) 2012  Inria and Microsoft Corporation
 *)

(* Test harness for schedule.ml *)

(* ocamlc -g unix.cma schedule.mli schedule.ml test_schedule.ml *)

open Printf;;

open Schedule;;

let timeout_cont name () =
  printf ">>> %s: timeout\n%!" name;
  Timeout
;;

let show_cont name () =
  printf ">>> %s: running\n%!" name;
  Continue (timeout_cont name, 60.0)
;;

let string_of_result r =
  match r with
  | Finished -> "Finished"
  | Stopped_kill -> "Stopped_kill"
  | Stopped_timeout -> "Stopped_timeout"
;;

let done_cont name success res time =
  printf ">>> %s: done (%s)\n%!" name (string_of_result res);
  if res = Finished then
    success
  else
    false
;;

let compute name delay result =
  function () ->
    if delay = 0 then begin
      printf "%s: immediate %B\n%!" name result;
      Immediate result
    end else begin
      Todo {
        line = sprintf "echo start %s %ds; sleep %d; echo end %s %B"
                       name delay delay name result;
        timeout = 10.0;
        timec = show_cont name;
        donec = done_cont name result;
      }
    end
;;

let tasks = [
  1, [compute "1-zenon" 4 true;
      compute "1-isa" 20 true;
      compute "1-smt" 5 true;
     ];
  2, [compute "2-zenon" 30 true;
      compute "2-isa" 40 true;
      compute "2-smt" 8 true;
     ];
  3, [compute "3-zenon" 80 true;
      compute "3-isa" 35 true;
      compute "3-smt" 8 false;
     ];
  4, [compute "4-zenon" 8 false;
      compute "4-isa" 8 true;
      compute "4-smt" 8 false;
     ];
  5, [compute "5-zenon" 80 false;
      compute "5-isa" 80 false;
      compute "5-smt" 80 true;
      compute "5-smt2" 30 true;
     ];
];;

Schedule.run (int_of_string Sys.argv.(1)) (Some Unix.stdin) tasks;;
