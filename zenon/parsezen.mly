/*  Copyright 2005 INRIA  */

%{

open Printf;;

open Expr;;
open Namespace;;
open Phrase;;

let rec myfold f e el =
  match el with
  | [] -> e
  | h::t -> f (e, myfold f h t)
;;

let mkand e el = myfold eand e el;;
let mkor e el = myfold eor e el;;
let mkimply e el = myfold eimply e el;;
let mkequiv e el = myfold eequiv e el;;
let mkrimply e el = myfold (fun (a, b) -> eimply (b, a)) e el;;

let mk_eall (vars, typ, body) =
  let f v b = eall (evar v, typ, b) in
  List.fold_right f vars body
;;

let mk_eex (vars, typ, body) =
  let f v b = eex (evar v, typ, b) in
  List.fold_right f vars body
;;

let mk_elam (vars, typ, body) =
  let f v b = elam (evar v, typ, b) in
  List.fold_right f vars body
;;

let mk_pattern constr vars body =
  mk_elam (vars, "", eapp ("$match-case", [evar constr; body]))
;;

let hyp_counter = ref 0;;
let gen_hyp_name () =
  incr hyp_counter;
  sprintf "%s%d" anon_prefix !hyp_counter
;;

let mk_string s = evar ("\"" ^ s ^ "\"");;

%}

%token OPEN
%token CLOSE
%token EOF

%token <string> IDENT
%token <string> STRING
%token <int> INT

%token ALL
%token AND
%token DEF
%token EQUAL
%token EQUIV
%token EX
%token FALSE
%token FIX
%token FIXPOINT
%token GOAL
%token HYP
%token IMPLY
%token INCLUDE
%token INDSET
%token INDPROP
%token LAMBDA
%token LET
%token MATCH
%token NOT
%token OR
%token RIMPLY
%token SELF
%token SIG
%token TAU
%token TRUE

%start file
%type <Phrase.zphrase list> file

%%

file:
  | EOF               { [] }
  | phrase file       { $1 :: $2 }
;

phrase:
  | DEF hyp_name OPEN IDENT ident_list CLOSE expr
      { let idl = List.map evar $5 in Zdef (DefReal ($2, $4, idl, $7, None)) }
  | FIXPOINT hyp_name IDENT OPEN IDENT ident_list CLOSE expr
      { let idl = List.map evar $6 in
        Zdef (DefReal ($2, $5, idl, $8, Some $3))
      }
  | HYP int_opt hyp_name expr
      { Zhyp ($3, $4, $2) }
  | GOAL expr
      { Zhyp (goal_name, enot $2, 0) }
  | SIG IDENT OPEN string_list CLOSE STRING
      { Zsig ($2, $4, $6) }
  | INDSET IDENT OPEN ident_list CLOSE OPEN constr_list CLOSE
      { Zinductive ($2, $4, $7, $2 ^ "_ind") }
  | INCLUDE STRING
      { Zinclude ($2) }
;

expr:
  | IDENT                                { evar $1 }
  | STRING                               { eapp ("$string", [mk_string $1]) }
  | OPEN IDENT expr_list CLOSE           { eapp ($2, $3) }
  | OPEN NOT expr CLOSE                  { enot ($3) }
  | OPEN AND expr expr_list CLOSE        { mkand $3 $4 }
  | OPEN OR expr expr_list CLOSE         { mkor $3 $4 }
  | OPEN IMPLY expr expr_list CLOSE      { mkimply $3 $4 }
  | OPEN RIMPLY expr expr_list CLOSE     { mkrimply $3 $4 }
  | OPEN EQUIV expr expr_list CLOSE      { mkequiv $3 $4 }
  | OPEN TRUE CLOSE                      { etrue }
  | TRUE                                 { etrue }
  | OPEN FALSE CLOSE                     { efalse }
  | FALSE                                { efalse }
  | OPEN ALL mlambda CLOSE               { mk_eall $3 }
  | OPEN EX mlambda CLOSE                { mk_eex $3 }
  | mlambda                              { mk_elam $1 }
  | OPEN TAU lambda CLOSE                { etau $3 }
  | OPEN EQUAL expr expr CLOSE           { eapp ("=", [$3; $4]) }
  | OPEN MATCH expr case_list CLOSE      { eapp ("$match", $3 :: $4) }
  | OPEN LET id_expr_list_expr CLOSE     { eapp ("$let", $3) }
  | OPEN FIX mlambda expr_list CLOSE     { eapp ("$fix", mk_elam $3 :: $4) }
;

expr_list:
  | expr expr_list     { $1 :: $2 }
  | /* empty */        { [] }
;

lambda:
  | OPEN OPEN IDENT STRING CLOSE expr CLOSE      { (evar $3, $4, $6) }
  | OPEN OPEN IDENT CLOSE expr CLOSE             { (evar $3, univ_name, $5) }
;

mlambda:
  | OPEN OPEN ident_list STRING CLOSE expr CLOSE { ($3, $4, $6) }
  | OPEN OPEN ident_list CLOSE expr CLOSE        { ($3, univ_name, $5) }
;

ident_list:
  | /* empty */       { [] }
  | IDENT ident_list  { $1 :: $2 }
;

int_opt:
  | /* empty */       { 1 }
  | INT               { $1 }
;

hyp_name:
  | STRING            { $1 }
;

string_list:
  | /* empty */         { [] }
  | STRING string_list  { $1 :: $2 }
;

case_list:
  | /* empty */
      { [] }
  | OPEN IDENT ident_list CLOSE expr case_list
      { mk_pattern $2 $3 $5 :: $6 }
;

id_expr_list_expr:
  | expr
      { [$1] }
  | IDENT expr id_expr_list_expr
      { match $3 with
        | [] -> assert false
        | body :: vals -> elam (evar ($1), "", body) :: $2 :: vals
      }
;

constr_list:
  | /* empty */
      { [] }
  | OPEN IDENT string_or_self_list CLOSE constr_list
      { ($2, $3) :: $5 }
;

string_or_self_list:
  | /* empty */                 { [] }
  | STRING string_or_self_list  { Param $1 :: $2 }
  | SELF string_or_self_list    { Self :: $2 }
;

%%
