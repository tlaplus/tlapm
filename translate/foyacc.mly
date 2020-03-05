%{
open Fotypes;;

let rec introduceVars vlist form = match vlist with
  | head::tail -> introduceVars tail ( Fofunctions.subst form (Constant(head)) (Variable(head)) )
  | [] -> form
  ;;
  
(* checks whether a string represents a variable *)
let isVariable str = (Fofunctions.isUpper (str.[0]))
   ;;

%}

%token TOK_EOF
%token <string> TOK_IDENT
%token TOK_LPAR
%token TOK_RPAR
%token TOK_LBRACKET
%token TOK_RBRACKET
%token TOK_NOT
%token TOK_CONJ
%token TOK_DISJ
%token TOK_IMPL
%token TOK_EQUIV
%token TOK_COMMA
%token TOK_FORALL
%token TOK_EXISTS
%token TOK_ALWAYS
%token TOK_ALWAYSP
%token TOK_SOMETIME
%token TOK_SOMETIMEP
%token TOK_NEXT
%token TOK_UNTIL
%token TOK_TRUE
%token TOK_FALSE
%token TOK_UNLESS

%left TOK_UNTIL
%left TOK_UNLESS
%left TOK_EQUIV
%left TOK_DISJ
%left TOK_IMPL
%left TOK_CONJ
%left TOK_NOT Quantification
%left TOK_SOMETIME
%left TOK_ALWAYS
%left TOK_NEXT
%start start
%type <Fotypes.formula> start

%%

start:  formula TOK_EOF
           {
               $1;
           }

formula: atom        {$1}
       | quantified  {$1}
       | connective  {$1}
       ;

atom: TOK_IDENT
        {
	   Literal(Atom($1,[]))
        }
    | TOK_IDENT TOK_LPAR termlist TOK_RPAR
        {
	    Literal(Atom($1,$3))
        }
    ;

quantified: TOK_FORALL boundvars formula %prec Quantification
              {
	         let f = introduceVars $2 $3 in
	         Forall($2, f)
              }
          | TOK_EXISTS boundvars formula %prec Quantification
              {
	         let f = introduceVars $2 $3 in
	         Exists($2, f)
              }
          ;

boundvars: TOK_LBRACKET varlist TOK_RBRACKET
           {
               $2
           }
          
varlist: TOK_IDENT
           {
	       if not (isVariable $1)
	       then
	         (print_string ($1^ " is not uppercase\n"); 
		 raise Parsing.Parse_error; 
		 (* return any string *)
		 ["nonesense"])
	       else
	       [$1]
           }
       | TOK_IDENT TOK_COMMA varlist
           {
	       $1::$3
           }
       ;
        
connective: TOK_TRUE 
              {
	         True
	      }
	  | TOK_FALSE
	      {
	         False
	      }
          | TOK_NOT formula 
              {
	          Not($2)
              }        
          | formula TOK_CONJ formula 
              {
	         And($1,$3)
              }
          | formula TOK_DISJ formula 
              {
	         Or($1,$3)
              }
          | formula TOK_IMPL formula 
              {
	         Implies($1,$3)
              }
          | formula TOK_EQUIV formula 
              {
	         And(Implies($1,$3),Implies($3,$1))
              }
	  | TOK_ALWAYS formula 
	      {
	         Always($2)
	      }
	  | TOK_ALWAYSP formula 
	      {
	         AlwaysP($2)
	      }
	  | TOK_SOMETIME formula 
	      {
	         Sometime($2)
	      }
	  | TOK_SOMETIMEP formula 
	      {
	         SometimeP($2)
	      }
	  | TOK_NEXT formula 
	      {
	         Next($2)
	      }
	  | formula TOK_UNTIL formula
	      {
	         Until($1, $3)
	      }
	  | formula TOK_UNLESS formula
	      {
	         Unless($1, $3)
	      }
          | TOK_LPAR formula TOK_RPAR
              {
                  $2;
              }
          ;

termlist: term 
            {
	       [$1]
            }
        | term TOK_COMMA termlist
            {
	       $1::$3
            }
        ;

term: TOK_IDENT
        {
	   Constant($1)
        }
    ;
