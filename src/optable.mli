(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

(* tla_parser.ml *)
type fixity =
  | Nonfix
  | Prefix | Postfix
  | Infix of assoc

and assoc =
  | Left | Non | Right

and dom =
    (* primitive operators *)
  | Logic | Sets | Modal
    (* user-definable operators *)
  | User
type prec = int * int
type tlaop = {
    name: string;
    prec: prec;
    fix: fixity;
    dom: dom;
    defn: Builtin.builtin option;
}
val optable: (string, tlaop) Hashtbl.t

(* fmt.ml *)
val lookup: string -> tlaop
val standard_form: Builtin.builtin -> tlaop
