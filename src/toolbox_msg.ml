(* This module handles the output of messages to the Toolbox.

It depends only on modules `Ext` and `Loc`.

Copyright (C) 2011  INRIA and Microsoft Corporation
*)
open Printf
open Ext


let delim = "@!!"

let print_begin typ =
    eprintf "%sBEGIN\n" delim;
    eprintf "%stype:%s\n" delim typ


let print_string name str = eprintf "%s%s:%s\n" delim name str
let print_int name n = eprintf "%s%s:%d\n" delim name n
let print_bool name b = eprintf "%s%s:%b\n" delim name b


let print_end () = eprintf "%sEND\n\n%!" delim


let print_warning msg =
    print_begin "warning";
    print_string "msg" msg;
    print_end ()


let print_error msg url =
    print_begin "error";
    print_string "url" url;
    print_string "msg" msg;
    print_end ()


let print_obligationsnumber n =
    print_begin "obligationsnumber";
    print_int "count" n;
    print_end ()


let line loc = Loc.line loc
let col loc = Loc.column loc


let print_obligation
        ~id ~loc ~status ~fp ~prover
        ~meth ~reason ~already ~obl =
    print_begin "obligation";
    print_int "id" id;
    let start = loc.Loc.start in
    let stop = loc.Loc.stop in
    eprintf "%sloc:%d:%d:%d:%d\n" delim
        (line start) (col start) (line stop) (col stop);
    print_string "status" status;
    Option.iter (print_string "fp") fp;
    Option.iter (print_string "prover") prover;
    Option.iter (print_string "meth") meth;
    Option.iter (print_string "reason") reason;
    Option.iter (print_bool "already") already;
    Option.iter (print_string "obl") obl;
    print_end ()
