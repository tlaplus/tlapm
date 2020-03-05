(*  Copyright 2004 INRIA  *)

open Printf;;

type condition =
  | Count of int * bool
  | String of string
;;

let cond = ref (Count (0, false));;

let str_tail s =
  String.sub s 1 (String.length s - 1)
;;

let cmp_forms (f1, g1) (f2, g2) =
  compare (Index.get_number f1) (Index.get_number f2)
;;

let print_forms b fgs =
  let f init (e, g) =
    bprintf b "%s[%d/%d]" init (Index.get_number e) g;
    Print.expr_soft (Print.Buff b) e;
  in
  match fgs with
  | [] | [_] -> List.iter (f "") fgs;
  | _ -> List.iter (f "\n    ") fgs;
;;

let rec pause () =
  eprintf " ###> ";
  flush stderr;
  let l = read_line () in
  let len = String.length l in
  if len = 0 then Count (0, false)
  else begin
    match l.[0] with
    | '0' .. '9' -> Count (int_of_string l, false)
    | '/' -> String (str_tail l)
    | '.' when len = 1 -> Count (0, true)
    | '.' -> Count (int_of_string (str_tail l), true)
    | 'q' -> failwith "exit"
    | 'd' ->
        eprintf "display current branch:\n";
        let b = Buffer.create 1000 in
        print_forms b (List.sort cmp_forms (Index.get_all ()));
        Buffer.output_buffer stderr b;
        pause ()
    | _ ->
       fprintf stderr "please type [.]<num> or /<string> or d or q\n";
       flush stderr;
       pause ()
  end
;;

let b = Buffer.create 1000;;

let ifstep action =
  if !Globals.debug_flag then begin
    match !cond with
    | Count (n, silent) when n > 0 ->
       if not silent then begin
         Buffer.reset b;
         action b;
         Buffer.output_buffer stderr b;
         eprintf "\n";
         flush stderr;
       end;
       cond := Count (n-1, silent);
    | Count (_, _) ->
       Buffer.reset b;
       action b;
       Buffer.output_buffer stderr b;
       cond := pause ();
    | String s ->
       Buffer.reset b;
       action b;
       let msg = Buffer.contents b in
       Buffer.output_buffer stderr b;
       if Misc.occurs s msg then cond := pause () else eprintf "\n";
       flush stderr;
  end;
;;

let forms msg fs =
  ifstep (fun b ->
    bprintf b "#### %s: " msg;
    print_forms b fs;
  )
;;

let rule msg r =
  ifstep (fun b ->
    bprintf b "#### %s: " msg;
    Print.mlproof_rule_soft (Print.Buff b) r;
    bprintf b " ";
  )
;;
