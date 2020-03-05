(*  Copyright 2005 INRIA  *)
{

open Lexing;;
open Parsezen;;
open Printf;;

}

let newline = ('\010' | '\013' | "\013\010")
let space = [' ' '\009' '\012']
let idstart = ['A'-'Z' 'a'-'z' '_' '0'-'9']
let idchar =  ['A'-'Z' 'a'-'z' '0'-'9' '_' '\'' '.']
let stringchar = [^ '\000'-'\031' '\"' '\\' '\127'-'\255']
let hexdigit = ['0'-'9' 'A'-'F' 'a'-'f']
let stringescape = '\\' (['a' 'b' 'f' 'n' 'r' 't' 'v' '\'' '\"' '\\' '?'] |
                         ('x' hexdigit hexdigit))

rule token = parse
  | '#' [^ '\010' '\013'] * { token lexbuf }
  | ';' [^ '\010' '\013'] * { token lexbuf }
  | newline     {
      lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with
        pos_bol = lexbuf.lex_curr_p.pos_cnum;
        pos_lnum = lexbuf.lex_curr_p.pos_lnum + 1;
      };
      token lexbuf
    }
  | space +     { token lexbuf }
  | "("         { OPEN }
  | ")"         { CLOSE }
  | '$' ['0' - '9'] + {
      let s = Lexing.lexeme lexbuf in
      let i = int_of_string (String.sub s 1 (String.length s - 1)) in
      INT i
    }

  | "$def"      { DEF }
  | "$fix"      { FIX }
  | "$fixpoint" { FIXPOINT }
  | "$goal"     { GOAL }
  | "$hyp"      { HYP }
  | "$include"  { INCLUDE }
  | "$indset"   { INDSET }
  | "$indprop"  { INDPROP }
  | "$let"      { LET }
  | "$match"    { MATCH }
  | "$self"     { SELF }
  | "$sig"      { SIG }

  | "-."        { NOT }
  | "/\\"       { AND }
  | "\\/"       { OR }
  | "=>"        { IMPLY }
  | "<="        { RIMPLY }
  | "<=>"       { EQUIV }
  | "T."        { TRUE }
  | "F."        { FALSE }
  | "A."        { ALL }
  | "E."        { EX }
  | "t."        { TAU }
  | "="         { EQUAL }

  | "\"" (stringchar | stringescape)* "\"" {
      let s = Lexing.lexeme lexbuf in
      STRING (String.sub s 1 (String.length s - 2))
    }

  | "\"" (stringchar | stringescape)* "\\" stringchar {
      let s = Lexing.lexeme lexbuf in
      let msg = sprintf "bad escape in string: \\%c" s.[String.length s - 1] in
      raise (Error.Lex_error msg)
    }

  | "\"" (stringchar | stringescape)* "\\"? _ {
      let s = Lexing.lexeme lexbuf in
      let c = String.escaped (String.sub s (String.length s - 1) 1) in
      let msg = sprintf "bad character in string: %s" c in
      raise (Error.Lex_error msg)
    }

  | idstart idchar* { IDENT (Lexing.lexeme lexbuf) }

  | eof         { EOF }
  | _ {
      let msg = sprintf "bad character %C" (Lexing.lexeme_char lexbuf 0) in
      raise (Error.Lex_error msg)
    }
