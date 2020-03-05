
{
open Fotypes
open Foyacc (* tokens *)
exception Eof

let currentLine = ref 1
let lineStartPos = ref 0
let posmin = ref 0 (*position*)
let posmax = ref 0 (*position de l'erreur*)


let update_line lexbuf = (*change line*)
	incr currentLine;
	lineStartPos := Lexing.lexeme_start lexbuf (*returns the position in the input stream of the first character of the matched string*)

let get = Lexing.lexeme

let update_pos str =
	posmin := (Lexing.lexeme_start str) - !lineStartPos + 1;
	posmax := (Lexing.lexeme_end str) - !lineStartPos + 1

let error buf callerID =
        print_endline callerID;
	update_pos buf;
	raise Parsing.Parse_error
}

let spaces = [ ' ' '\t' '\r']
let ident = ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '0'-'9' '_' ]*
let comment = (';'(_#'\n')*)


rule lexer = parse
    spaces          {update_pos lexbuf; lexer lexbuf} (* Eat up spaces/endlines *)
  | comment         {update_pos lexbuf; lexer lexbuf}
  | '\n'            {update_line lexbuf; lexer lexbuf}
  | "("             {update_pos lexbuf; TOK_LPAR}
  | ")"             {update_pos lexbuf; TOK_RPAR}
  | "["             {update_pos lexbuf; TOK_LBRACKET}
  | "]"             {update_pos lexbuf; TOK_RBRACKET}
  | "~"             {update_pos lexbuf; TOK_NOT}
  | "not"           {update_pos lexbuf; TOK_NOT}
  | "&"             {update_pos lexbuf; TOK_CONJ}
  | "|"             {update_pos lexbuf; TOK_DISJ}
  | "=>"            {update_pos lexbuf; TOK_IMPL}
  | "->"            {update_pos lexbuf; TOK_IMPL}
  | "<=>"           {update_pos lexbuf; TOK_EQUIV}
  | "<->"           {update_pos lexbuf; TOK_EQUIV}
  | ","             {update_pos lexbuf; TOK_COMMA}
  | "!"             {update_pos lexbuf; TOK_FORALL}
  | "?"             {update_pos lexbuf; TOK_EXISTS}
  | "always"        {update_pos lexbuf; TOK_ALWAYS}
  | "alwaysp"        {update_pos lexbuf; TOK_ALWAYSP}
  | "sometime"      {update_pos lexbuf; TOK_SOMETIME}
  | "sometimep"      {update_pos lexbuf; TOK_SOMETIMEP}
  | "next"          {update_pos lexbuf; TOK_NEXT}
  | "until"         {update_pos lexbuf; TOK_UNTIL}
  | "unless"        {update_pos lexbuf; TOK_UNLESS}
  | "True"          {update_pos lexbuf; TOK_TRUE}
  | "False"         {update_pos lexbuf; TOK_FALSE}
  | "skolem"        {error lexbuf "skolem is a reserved word"}
  | "hidden"        {error lexbuf "hidden is a reserved word"}
  | "constant"      {error lexbuf "constant is a reserved word"}
  | "NV_V"['a'-'z' 'A'-'Z' '0'-'9' '_' ]*     {error lexbuf "NV_V cannot start any word: reserved"}
  | "NVV"['a'-'z' 'A'-'Z' '0'-'9' '_' ]*     {error lexbuf "NVV cannot start any word: reserved"}
  | ident           {update_pos lexbuf; TOK_IDENT (Lexing.lexeme lexbuf)}
  | eof             {TOK_EOF}
  | _               {error lexbuf ""}
