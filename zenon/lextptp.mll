(*  Copyright 2005 INRIA  *)
{

open Lexing;;
open Parsetptp;;
open Printf;;

let rec count_lf i s accu =
  if i >= String.length s then accu
  else count_lf (i+1) s (if s.[i] = '\n' then accu + 1 else accu)
;;

let adjust_pos lexbuf =
  let lx = Lexing.lexeme lexbuf in
  let rec loop i nl last =
    if i >= String.length lx then (nl, last)
    else if lx.[i] = '\n' then loop (i+1) (nl+1) i
    else loop (i+1) nl last
  in
  let (nl, last) = loop 0 0 0 in
  if nl > 0 then begin
    lexbuf.lex_curr_p <- {
      lexbuf.lex_curr_p with
      pos_bol = Lexing.lexeme_start lexbuf + last + 1;
      pos_lnum = lexbuf.lex_curr_p.pos_lnum + nl;
    }
  end;
;;

}

let space = [' ' '\009' '\012' '\013']
let stringchar = [^ '\000'-'\031' '\'' '\127'-'\255']
let upperid = [ 'A' - 'Z' ]
let lowerid = [ 'a' - 'z' ]
let idchar = [ 'A' - 'Z' 'a' - 'z' '0' - '9' '_' ]

rule token = parse
  | "%@" ([^ '\010']* as annot)
                     { ANNOT annot }
  | "%" [^ '\010']*
                     { token lexbuf }
  | '\010'           { adjust_pos lexbuf; token lexbuf }
  | "/*" ([^ '*']* | '*'+ [^ '/' '*'])* '*'+ '/' {
     adjust_pos lexbuf;
     token lexbuf
    }
  | space +          { token lexbuf }
  | "("              { OPEN }
  | ")"              { CLOSE }
  | "["              { LBRACKET }
  | "]"              { RBRACKET }
  | ","              { COMMA }
  | ":"              { COLON }
  | "."              { DOT }
  | "?"              { EX }
  | "!"              { ALL }
  | "~"              { NOT }
  | "|"              { OR }
  | "&"              { AND }
  | "=>"             { IMPLY }
  | "<="             { RIMPLY }
  | "<=>"            { EQUIV }
  | "="              { EQSYM }
  | "!="             { NEQSYM }
  | "<~>"            { XOR }
  | "~|"             { NOR }
  | "~&"             { NAND }
  | "include"        { INCLUDE }
  | "cnf"            { INPUT_CLAUSE }
  | "fof"            { INPUT_FORMULA }
  | "$true"          { TRUE }
  | "$false"         { FALSE }
  | "\'"             { single_quoted (Buffer.create 20) lexbuf }
  | "\""             { double_quoted (Buffer.create 20) lexbuf }
  | lowerid idchar * { LIDENT (Lexing.lexeme lexbuf) }
  | upperid idchar * { UIDENT (Lexing.lexeme lexbuf) }

  | ['+' '-']? ['0' - '9']+
       ('.' ['0' - '9']+)?
       (['E' 'e'] ['+' '-']? ['0' - '9']+)?
    { LIDENT (Lexing.lexeme lexbuf) }
  | ['+' '-']? ['0' - '9']+ '/' ['0' - '9']+ { LIDENT (Lexing.lexeme lexbuf) }

  | eof              { EOF }
  | _                {
      let msg = sprintf "bad character %C" (Lexing.lexeme_char lexbuf 0) in
      raise (Error.Lex_error msg)
    }

and single_quoted buf = parse
  | '\\' [ '\\' '\'' ] {
      Buffer.add_char buf (Lexing.lexeme_char lexbuf 1);
      single_quoted buf lexbuf
    }
  | [' ' - '&' (* ' *) '(' - '[' (* \ *) ']' - '~' ]+ {
      Buffer.add_string buf (Lexing.lexeme lexbuf);
      single_quoted buf lexbuf
    }
  | '\'' { LIDENT (Buffer.contents buf) }
  | '\\' { raise (Error.Lex_error "bad \\ escape in <single_quoted>") }
  | _ { raise (Error.Lex_error "bad character in <single_quoted>") }

and double_quoted buf = parse
  | '\\' [ '\\' '\"' ] {
      Buffer.add_char buf (Lexing.lexeme_char lexbuf 1);
      double_quoted buf lexbuf
    }
  | [' ' - '!' (* "" *) '#' - '[' (* \ *) ']' - '~' ]+ {
      Buffer.add_string buf (Lexing.lexeme lexbuf);
      double_quoted buf lexbuf
    }
  | '\"' { STRING (Buffer.contents buf) }
  | '\\' { raise (Error.Lex_error "bad \\ escape in <distinct_object>") }
  | _ { raise (Error.Lex_error "bad character in <distinct_object>") }
