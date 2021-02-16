(*
 * printing error messages
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

exception Fatal;;

let loc_to_string at =
  match at with
  | None -> ""
  | Some w ->
     match Util.query_locus w with
     | None -> ""
     | Some loc -> Loc.string_of_locus loc ^ " :\n"
;;

let info ?at fmt =
  let k s = Printf.eprintf "%s%s\n%!" (loc_to_string at) s in
  Format.ksprintf k fmt
;;

let warnbuf = Buffer.create 80;;
Buffer.add_char warnbuf '\n';;

let warn ?at fmt =
  let k s =
    Printf.eprintf "%s%s\n%!" (loc_to_string at) s;
    Printf.bprintf warnbuf "\\* %s\n" s;
  in
  Format.ksprintf k fmt
;;

let get_warnings () =
  let res = Buffer.contents warnbuf in
  Buffer.clear warnbuf;
  Buffer.add_char warnbuf '\n';
  res
;;

let set_warnings s =
  Buffer.clear warnbuf;
  Buffer.add_string warnbuf s;
;;

let aux url ?at msg =
  let locus = loc_to_string at in
  if !Params.toolbox then
    match url with
    | None -> Toolbox_msg.print_warning (locus ^ msg);
    | Some u -> Toolbox_msg.print_error (locus ^ msg) u;
  else begin
    Printf.eprintf "%s%s\n%!" locus msg;
    match url with
    | None -> ()
    | Some u -> Printf.eprintf "Please report this problem to %s\n%!" u
  end;
;;

let err ?at fmt = Format.ksprintf (fun x -> aux None ?at x) fmt;;

let fatal ?at fmt =
  let f x =
    aux None ?at (x ^ "\nAborting.");
    raise Fatal;
  in
  Format.ksprintf f fmt;
;;

let bug ?at msg =
  Printf.eprintf "%s%s\n%!" (loc_to_string at) msg;
  assert false;
;;

(********** old stuff ********* FIXME convert all uses to new stuff *)

let loc : string option ref = ref None
let msg : string option ref = ref None
let warning = ref false

let sget v =
  match v with
    | None -> ""
    | Some v -> v

let set st mesg =
loc :=
  begin match (Util.query_locus st) with
    | None ->
        None
    | Some loc ->
        Some (Loc.string_of_locus ~cap:true loc)
  end;
msg := Some (mesg^"\n\n"^(sget !msg))
;;
