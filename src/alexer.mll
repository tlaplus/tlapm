(*
alexer.mll --- lexer

Copyright (C) 2008-2010  INRIA and Microsoft Corporation
*)
{

  open Lexing
  open Pars
  open Tla_parser.Token

  module E = Error
  exception Error of E.t

  let eol lexbuf =
    let (start, curr) = (lexbuf.lex_start_p, lexbuf.lex_curr_p) in
      lexbuf.lex_curr_p <- { curr with
                               pos_lnum = curr.pos_lnum + 1 ;
                               pos_bol  = curr.pos_cnum }

  let tab_complain lexbuf =
    let e = E.error (Loc.locus_of_position lexbuf.lex_start_p) in
    let e =
      E.err_set_unexpected "TAB character. TLAPS does not handle TAB \
                            characters in source files." e
    in
    raise (Error e)

}

let whitesp  = [' ']
let tab      = '\t'
let newline  = ('\r' | '\n' | "\r\n")

let letter   = ['a'-'z' 'A'-'Z']
let numeral  = ['0'-'9']
let namechar = (letter | numeral | '_')

let name     = namechar* letter namechar*

let keyword = (
  "ASSUME"|"ASSUMPTION"|"AXIOM"|"BOOLEAN"|"CASE"|"CHOOSE"|"CONSTANT"
  |"CONSTANTS"|"BY"|"DEF"|"DEFINE"|"DEFS"|"LAMBDA"|"OBVIOUS"|"ELSE"
  |"EXCEPT"|"EXTENDS"|"IF"|"IN"|"INSTANCE"|"LET"|"HAVE"|"TRUE"|"FALSE"
  |"HIDE"|"PROOF"|"PROVE"|"STATE"|"OMITTED"|"LOCAL"|"MODULE"|"OTHER"
  |"THEN"|"THEOREM"|"UNCHANGED"|"QED"|"RECURSIVE"|"WITNESS"|"STRING"
  |"SUFFICES"|"ACTION"|"LEMMA"|"COROLLARY"|"VARIABLE"|"VARIABLES"|"WITH"
  |"TAKE"
  |"USE"|"PICK"|"NEW"|"TEMPORAL"|"PROPOSITION"|"ONLY")

rule modfile = parse
  | "----" '-'* ' '* "MODULE"
      { [ PUNCT "----"; KWD "MODULE" ] }
  | newline
      { eol lexbuf ; modfile lexbuf }
  | _ { modfile lexbuf }
  | eof { [] }

and token = parse

  (* whitespace *)
  | whitesp            { token lexbuf }
  | newline            { eol lexbuf ; token lexbuf }
  | tab                { tab_complain lexbuf }

  (* pragmas *)
  | ("(*{"|"}*)" as prag)
      { [ PUNCT prag ] }

  (* comments *)
  | "\\*"
      { linecom lexbuf }
  | "(*"
      { comment 1 lexbuf }

  (* exceptions *)
  | ("[]" as op)
      { [ OP op ] }
  | ("(+)"|"(-)"|"(/)"|"(\\X)"|"(.)" as op)
      { [ OP op ] }

  (* strict punctuation *)
  | "----" '-'*
      { [ PUNCT "----" ] }
  | "====" '='*
      { [ PUNCT "====" ] }

  | "<*>" ('.'* as dots)
      { [ ST ( `Star, "", String.length dots) ] }
  | "<+>" ('.'* as dots)
      { [ ST ( `Plus, "", String.length dots) ] }
  | '<' (numeral+ as num) '>' (namechar* as lab) ('.'* as dots)
      { [ ST (`Num (int_of_string num), lab, String.length dots) ] }

  | (","|"."|"_"|"("|")"|"["|"]"|"{"|"}"|"<<"|">>"|"]_"|">>_"|"=="|"!"
    |"@"|":"|"::"|";"|"->"|"<-"|"|->"|"\\A"|"\\AA"|"\\E"|"\\EE"|'_'
    |"\\forall"|"\\exists" as p)
      { [ PUNCT p ] }

  (* numbers *)
  | (numeral+ as ch) '.' (numeral+ as man)
      { [ NUM (ch, man) ] }
  | (numeral+ as i)
      { [ NUM (i, "") ] }
  | "\\b" (['0' '1']+ as b)
      { let b = "0b" ^ b in
        [ NUM (string_of_int (int_of_string b), "") ] }
  | "\\o" (['0'-'7']+ as o)
      { let o = "0o" ^ o in
        [ NUM (string_of_int (int_of_string o), "") ] }
  | "\\h" ((numeral | ['a'-'f' 'A'-'F'])+ as h)
      { let h = "0x" ^ h in
        [ NUM (string_of_int (int_of_string h), "") ] }

  (* strings *)
  | '\"'
      { string (Buffer.create 50) lexbuf }

  (* prefix operators *)
  | ("\\neg"|"\\lnot"|"~"|"-."|"<>"|"UNION"|"SUBSET"
    |"ENABLED"|"UNCHANGED"|"DOMAIN" as op)
      { [ OP op ] }

  (* postfix operators *)
  | ("'"|"^+"|"^*"|"^#" as op)
      { [ OP op ] }

  (* infix operators *)
  | (">="|"\\geq" |"<="|"=<"|"\\leq"|"#"|"/="|"\\oplus"|"\\ominus"|"\\otimes"
    |"\\oslash"|"\\odot"|"\\cap"|"\\intersect"|"\\cup"|"\\union"|"<=>"
    |"\\equiv"|"\\o"|"\\circ"|"\\X"|"\\times"|"=>"|"-+->"|"~>"|"/\\"|"\\land"
    |"\\/"|"\\lor"|"#"|"/="|"-|"|"::="|":="|"<"|"="|"=|"|">"|"\\approx"
    |"\\asymp"|"\\cong"|"\\doteq"|"\\gg"|"\\notin"|"\\ll"|"\\prec"|"\\preceq"
    |"\\propto"|"\\sim"|"\\simeq"|"\\sqsubset"|"\\sqsubseteq"|"\\sqsupset"
    |"\\sqsupseteq"|"\\subset"|"\\subseteq"|"\\succ"|"\\succeq"|"\\supset"
    |"\\supseteq"
    |"|-"|"|="|"\\cdot"|"@@"|":>"|"<:"|"\\"|"\\in"
    |".."|"..."|"!!"|"##"|"$"|"$$"|"??"|"\\sqcap"
    |"\\sqcup"|"\\uplus"|"\\wr"|"+"|"++"|"%"|"%%"|"|"
    |"||"|"--"|"-"|"&"|"&&"|"*"|"**"|"/"|"//"|"\\bigcirc"|"\\bullet"
    |"\\div"|"\\star"|"^"|"^^" as op)
      { [ OP op ] }

  (* names and reserved words *)

  (* WF_ and WF_ are treated as punctuation *)
  | ("WF_" | "SF_" as f) (keyword as kwd)
      { [ PUNCT f ; KWD kwd ] }
  | ("WF_" | "SF_" as f) (name as rest)
      { [ PUNCT f ; ID rest ] }
  | ("WF_"|"SF_" as f)
      { [ PUNCT f ] }

  | (keyword as kwd)
      { [ KWD kwd ] }

  | (name as nm)
      { [ ID nm ] }
      (* On the same match, the earlier rule fires, so WF_foo is always lexed
         as [WF_ ; foo] *)

  (* end of stream *)
  | eof
      { [ ] }

  (* everything else is an error *)
  | (_ as c)
      { let e = E.error (Loc.locus_of_position lexbuf.lex_start_p) in
        let e = E.err_set_unexpected (String.make 1 c) e in
          raise (Error e)
      }

and string sofar = parse
  | tab { tab_complain lexbuf }

  | newline {
      eol lexbuf ;
      let nl = Printf.sprintf "newline after %S" (Buffer.contents sofar) in
      let e = E.error (Loc.locus_of_position lexbuf.lex_start_p) in
      let e = E.err_set_unexpected nl e in
      raise (Error e)
    }

  | '\\' ['\"' '\\' 't' 'n' 'f' 'r'] as tok
      { Buffer.add_string sofar tok;
        string sofar lexbuf
      }
  | ('\\' ['0'-'7'] ['0'-'7'] ['0'-'7'] as tok)
      { Buffer.add_string sofar tok;
        string sofar lexbuf
      }
  | '"'
      { [ STR (Buffer.contents sofar) ] }

  | (_ as k)
      { Buffer.add_char sofar k;
        string sofar lexbuf }

and linecom = parse
  | tab             { tab_complain lexbuf }
  | newline         { eol lexbuf ; token lexbuf }
  | _               { linecom lexbuf }

and comment depth = parse
  | tab             { tab_complain lexbuf }
  | newline         { eol lexbuf ; comment depth lexbuf }
  | "*)"
      { if depth = 1 then
          token lexbuf
        else
          comment (depth - 1) lexbuf }
  | "(*"
      { comment (depth + 1) lexbuf }
  | _
      { comment depth lexbuf }

{

  (* FIXME use normal buffers instead *)
  let refill buf ic =
    try
      Buffer.clear buf ;
      let s = input_line ic in
      Buffer.add_string buf s ;
      Buffer.add_char buf '\n' ;
      true
    with
      | Error _ as e -> raise e
      | _ -> false


  let inch_reader ic =
    let buf = Buffer.create 80 in
    let get outs n =
      let rec read nread n =
        let nc = Buffer.length buf in
        if nc <= n then begin
          for i = 0 to nc - 1 do
            Bytes.set outs (nread + i) (Buffer.nth buf i)
          done ;
          if refill buf ic then
            read (nread + nc) (n - nc)
          else
            nread + nc
        end else begin
          for i = 0 to n - 1 do
            Bytes.set outs (nread + i) (Buffer.nth buf i)
          done ;
          let s = Buffer.sub buf n (Buffer.length buf - n) in
          Buffer.clear buf ;
          Buffer.add_string buf s ;
          nread + n
        end
      in read 0 n
    in get

  let marked_token lexfn lexbuf =
    let stuff = lexfn lexbuf in
    List.map begin fun t ->
      let locstart = Loc.locus_of_position lexbuf.lex_start_p in
      let locstop  = Loc.locus_of_position lexbuf.lex_curr_p in
      let loc = Loc.merge locstart locstop in
      { form = t ; rep = "" ; loc = loc }
    end stuff

  let lex_channel fn ich =
    let inited = ref false in
    let lb =
      let lb = Lexing.from_function (inch_reader ich) in
      (* lb.lex_start_p <- { lb.lex_start_p with pos_fname = fn } ; *)
      lb.lex_curr_p <- { pos_fname = fn ;
                         pos_cnum  = 0 ;
                         pos_lnum  = 1 ;
                         pos_bol   = 0
                       } ;
      lb
    in
    let buffer = ref [] in
    let next () = try begin
      if !buffer = [] then
        buffer := marked_token (if !inited then token else modfile) lb ;
      inited := true ;
      match !buffer with
        | t :: ts ->
            buffer := ts ;
            Some t
        | _ -> None
    end with Error e ->
      Error.print_error stderr e ;
      None
    in (LazyList.make next, Loc.locus_of_position lb.lex_curr_p)

  let lex fn =
    let ich =
      try Stdlib.open_in fn
      with Sys_error msg -> Errors.fatal "Cannot open file: %s" msg
    in
    lex_channel fn ich

  let lex_string ?(fn = "") s =
    let lb = Lexing.from_string s in
    lb.lex_curr_p <- {pos_fname = fn; pos_cnum = 0; pos_lnum = 1; pos_bol = 0};
    let buffer = ref [] in
    let next () =
      try
        if !buffer = [] then buffer := marked_token token lb;
        match !buffer with
          | t :: ts -> buffer := ts; Some t
          | _ -> None
      with Error e ->
        Error.print_error stderr e;
        None
    in (LazyList.make next, Loc.locus_of_position lb.lex_curr_p)

}
