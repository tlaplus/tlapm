(* This code derives from a GPL'ed code and so is GPL'ed *)
type variable = string
type constant = string
type skolem   = string

type varlist = variable list

type arg = Variable of variable
         | Constant of constant
	 | Skolem of skolem * varlist

type arglist = arg list

type atom = string

type literal = Atom of atom * arglist | NotAtom of atom * arglist ;;

type formula =  True                                 (* constants *)
              | False
	      | Literal of literal                   (* a literal *)
	      | And of formula * formula             (* Booleans *)
	      | Or  of formula * formula
	      | Implies  of formula * formula
	      | Not  of formula
	      | Forall of varlist * formula              (* Quantification*)
	      | Exists of varlist * formula
	      | Always of formula                    (* Temporal operators*)
	      | AlwaysP of formula
	      | Sometime of formula
	      | SometimeP of formula
	      | Next of formula
	      | Until of formula * formula
	      | Unless of formula * formula
(*
type disjunct = True
              | False
	      | Or of literal list

type cnf = True
         | False
	 | And of disjunct list

type formulaList = True
		 | False
		 | Literal of literal
		 | And of formulaList list
		 | Or of formulaList list
*)
