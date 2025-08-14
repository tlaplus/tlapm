(* Parsing errors.

Copyright (C) 2008-2010  INRIA and Microsoft Corporation
*)
open Ext

type error_ =
    { err_unex : string option ;
      err_exps : string list ;
      err_msgs : string list ;
      err_ints : string list }

type error = Error of error_ * Loc.locus
type t = error

(* FIXME make this return a string *)
let print_error ?(send_output = output_string) ?(verbose = false) ouch (Error (err, locus)) =
  let unexp =
    match err.err_unex with
      | None -> ""
      | Some s -> "Unexpected " ^ s ^ "\n"
  in
  let exps =
    match List.unique (err.err_exps) with
      | [] -> ""
      | exps ->
          "Expecting one of {" ^ String.concat ", " exps ^ "}\n"
  in
  let ints =
    if verbose then
      String.concat "" (List.map
                          (fun i -> "[Internal] " ^ i ^ "\n")
                          (List.unique err.err_ints))
    else ""
  in
  let msgs =
    String.concat "" (List.map
                        (fun i -> i ^ "\n")
                        (List.unique (err.err_msgs)))
  in
  let loc = Printf.sprintf "%s\n" (Loc.string_of_locus locus) in
  send_output ouch loc;
  send_output ouch unexp ;
  send_output ouch exps ;
  send_output ouch msgs ;
  send_output ouch ints ;
  flush ouch;

  Errors.set
    (Util.set_locus (Property.noprops err) locus)
    (unexp ^ exps ^ msgs ^ ints);

  if !Params.toolbox
  then Toolbox_msg.print_warning (loc ^ unexp ^ exps ^ msgs ^ ints)


let error locus =
  Error ({ err_unex = None ;
           err_exps = [] ;
           err_ints = [] ;
           err_msgs = [] }, locus)

let err_combine (Error (a, alocus)) (Error (b, blocus)) =
  let combo a b =
    { err_unex = None ;
      err_exps = a.err_exps @ b.err_exps ;
      err_ints = a.err_ints @ b.err_ints ;
      err_msgs = a.err_msgs @ b.err_msgs ;
    }
  in
    Error (combo a b, blocus)

let err_add_message msg (Error (e, elocus)) =
  Error ({ e with err_msgs = msg :: e.err_msgs }, elocus)

let err_add_internal i (Error (e, elocus)) =
  Error ({ e with err_ints = i :: e.err_ints }, elocus)

let err_add_expecting x (Error (e, elocus)) =
  Error ({ e with err_exps = x :: e.err_exps }, elocus)

let err_set_unexpected u (Error (e, elocus)) =
  Error ({ e with err_unex = Some u }, elocus)
