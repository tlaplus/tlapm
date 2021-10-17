(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

(* expr/fmt.ml *)
module Prec: Pars.Intf.Prec with
    type prec = int * int
module Fu: Fmtutil.Minimal_sig with
    module Prec = Prec
module Token : sig
    type token_ =
        | BOF  (* beginning of file *)
        | ID of string  (* identifiers *)
        | OP of string  (* operators *)
        | KWD of string  (* keywords *)
        | NUM of string * string  (* numbers *)
        | STR of string  (* strings *)
        | PUNCT of string  (* misc. punctuation *)
        | ST of
            [`Star | `Plus | `Num of int] *
            string * int
            (* step token *)
    and token = {
    form : token_;
    mutable rep : string;
    loc : Loc.locus;
  }
  (* include Pars.Intf.Tok *)
  val bof : Loc.locus -> token
  val rep : token -> string
  val locus : token -> Loc.locus
  val eq : token -> token -> bool
  val pp_print_token : Format.formatter -> token -> unit
end


module P :
    Pars.Pco.Make_sig with
        type Tok.token = Token.token and
        module Prec = Prec


(* expr/parser.ml *)
type pcx = {ledge: int; clean: bool}
type 'a prs = (pcx, 'a) P.prs
type 'a lprs = 'a prs Lazy.t
val locate: ('a, 'b) P.prs ->
    ('a, 'b Property.wrapped) P.prs
val anyident: (pcx, string) P.prs
val prefix: string -> (pcx, string) P.prs
val punct: string -> (pcx, string) P.prs
val anyop: (pcx, string) P.prs
val anyname: (pcx, string) P.prs
val nat: (pcx, int) P.prs
val kwd: string -> (pcx, string) P.prs
val infix: string -> (pcx, string) P.prs
val scan:
    (Token.token_ -> 'a option) ->
    (pcx, 'a) P.prs
val number: (pcx, string * string) P.prs
val ident: string -> (pcx, string) P.prs
val pragma:
    (pcx, 'a) P.prs -> (pcx, 'a) P.prs
val str: (pcx, string) P.prs
val anyprefix: (pcx, string) P.prs
val anypostfix: (pcx, string) P.prs
val anyinfix: (pcx, string) P.prs
val pickle: string -> string

(* module/save.ml *)
val init: pcx
