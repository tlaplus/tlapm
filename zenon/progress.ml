(*  Copyright 2005 INRIA  *)

open Printf;;

type progress = No | Bar | Msg;;
let level = ref Bar;;

let progress_cur = ref (-1);;
let progress_char = ref 0;;
let progress_anim = "/-\\|";;
let backspace = '\008';;

let do_progress f bar =
  match !level with
  | No -> ()
  | Bar ->
      let tm = Sys.time () in
      let cur = int_of_float (60. *. tm /. !Globals.time_limit) in
      if !progress_cur = -1 then begin
        eprintf "%s" (String.make 61 ' ');
        eprintf "%s" (String.make 60 backspace);
        progress_cur := 0;
      end;
      progress_char := (!progress_char + 1) mod (String.length progress_anim);
      if cur = !progress_cur + 1 then begin
        eprintf "%c*%c" backspace progress_anim.[!progress_char];
        progress_cur := cur;
      end else if cur > !progress_cur then begin
        eprintf "%c" backspace;
        for i = !progress_cur to cur - 1 do
          eprintf "%c" bar;
        done;
        eprintf "%c" (progress_anim.[!progress_char]);
        progress_cur := cur;
      end else begin
        eprintf "%c%c" backspace (progress_anim.[!progress_char]);
      end;
      flush stderr;
  | Msg ->
      flush stdout;
      flush stderr;
      f ();
      flush stdout;
      flush stderr;
;;

let end_progress msg =
  match !level with
  | No -> ()
  | Bar -> eprintf "\r"; flush stderr;
  | Msg -> if msg <> "" then (eprintf "%s\n" msg; flush stderr)
;;
