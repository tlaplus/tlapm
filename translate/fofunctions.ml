open Fotypes;;

exception Illegal1;;
exception Illegal2;;
exception Illegal3;;
exception Illegal4;;
exception Illegal5;;
exception Illegal6;;
exception Illegal7;;
exception NonMonodic;;

(******************************************************************)
(*                       DEBUGGING                                *)
(******************************************************************)
(* choose either of the following definitions *)
(*let debug str = print_string (str); print_newline ();;*)
let debug str = ();;


(******************************************************************)
(*                    GENERAL PURPOSE HELPERS                     *)
(******************************************************************)

(* Used in checks whether a string represents a variable *)
let isUpper = function
  | 'A' .. 'Z' -> true
  | _ -> false
  ;;
(* excludes an element from a list *)
(* not in Ocaml from RH 7.3 *)
let rec except e =
  function
    [] -> []
  | e'::l -> if e = e' then l else e'::(except e l)
  ;;

(* exclude a list from a list *)
let rec exceptL exceptionList aList =
  match exceptionList with
  [] -> aList
  | e'::l -> except e' (exceptL l aList)
  ;;

(* union of two lists *)
let rec union l1 l2 =
  match l1 with
  | [] -> l2
  | head::tail ->
     if List.mem head l2
     then union tail l2
     else head::(union tail l2)
  ;;


(******************************************************************)
(*                       PRINTING FUNCTIONS                       *)
(******************************************************************)
(* First of all, we define functions used to print all the objects *)
(* that occur in this program. These functions go first to simplify *)
(* debugging.*)

(* a list of variables to string *)
let rec string_of_v_list = function
 | [] -> ""
 | head::[] ->    head
 | head::tail ->  head ^ ", " ^ string_of_v_list tail
 ;;

(* a list of arguments to string *)
let string_of_arg = function
    | Variable(head) -> head
    | Constant(head) -> head
    | Skolem(head,vlist) -> let args = if List.length vlist = 0
                                then ""
				else "(" ^ string_of_v_list vlist ^ ")"
                            in head ^ args

(* Make a string out of a list of strings *)
let rec string_of_a_list = function
    | [] -> ""
    | head::[] -> string_of_arg head
    | head::tail -> string_of_arg head ^ ", " ^ string_of_a_list tail
    ;;

(* Formula to string *)
let rec string_of_formula = function
  | True -> (*debug("sof 1");*) "True"
  | False -> (*debug("sof 2");*) "False"
  | Literal(Atom(a,v)) -> (*debug("sof 3 " ^ a);*)
     if List.length v = 0
     then a
     else (a ^ "("^ string_of_a_list v ^")")
  | Literal(NotAtom(a,v)) -> (*debug("sof 4");*)
     if List.length v = 0
     then "not "^a
     else ("not " ^ a ^ "("^ string_of_a_list v ^")")
  | And(f,g) ->(*debug("sof 5");*)
     "("^string_of_formula f ^ " & " ^ string_of_formula g^")"
  | Or(f,g) -> (*debug("sof 6");*)
     "("^string_of_formula f ^ " | " ^ string_of_formula g^")"
  | Implies(f,g) -> (*debug("sof 7");*)
    "("^string_of_formula f ^ " => " ^ string_of_formula g^")"
  | Not(f) -> (*debug("sof 8");*)
    "not (" ^ string_of_formula f^")"
  | Forall(v,f) ->(*debug("sof 9");*)
    "![" ^ string_of_v_list v ^"](" ^ string_of_formula f^")"
  | Exists(v,f) -> (*debug("sof 10");*)
    "?[" ^ string_of_v_list v ^"](" ^ string_of_formula f^")"
  | Always(f) -> (*debug("sof 11");*)
    "always(" ^ string_of_formula f^")"
  | AlwaysP(f) -> (*debug("sof 12");*)
    "alwaysp(" ^ string_of_formula f^")"
  | Sometime(f) -> (*debug("sof 13");*)
    "sometime(" ^ string_of_formula f^")"
  | SometimeP(f) -> (*debug("sof 14");*)
    "sometimep(" ^ string_of_formula f^")"
  | Next(f) -> (*debug("sof 15");*)
    "next(" ^ string_of_formula f^")"
  | Until(f,g) -> (*debug("sof 16");*)
    "("^string_of_formula f ^ " until " ^ string_of_formula g^")"
  | Unless(f,g) -> (*debug("sof 17");*)
    "("^ string_of_formula f ^ " unless " ^ string_of_formula g^")"
  ;;

(* clause to string *)
let rec string_of_clause = function
    | [] -> ""
    | head::[]   -> string_of_formula head
    | head::tail -> string_of_formula head ^ ", " ^ string_of_clause tail
    ;;

(* list of formulas to string *)
let rec string_of_formulas = function
    | [] -> ""
    | head::[]   -> string_of_formula head
    | head::tail -> string_of_formula head ^ ",\n" ^ string_of_formulas tail
    ;;

(* initial clause set to string *)
let rec string_of_i_clausesAux = function
    | [] -> ""
    | head::[]  -> "or([" ^ string_of_clause head ^ "])"
    | head::tail  -> "or([" ^ string_of_clause head ^ "]), \n" ^
                                   string_of_i_clausesAux tail
    ;;
let string_of_i_clauses clauses =  string_of_i_clausesAux clauses;;

(* universal clause set to string *)
let rec string_of_u_clausesAux = function
    | [] -> ""
    | head::[]  -> "always(or([" ^ string_of_clause head ^ "]))"
    | head::tail  -> "always(or([" ^ string_of_clause head ^ "])), \n" ^
                                   string_of_u_clausesAux tail
    ;;
let string_of_u_clauses clauses =  string_of_u_clausesAux clauses;;

(* step clause set to string *)
let rec string_of_s_clausesAux = function
    | [] -> ""
    | head::[]  -> "always(or([" ^ string_of_clause head ^ "]))"
    | head::tail  -> "always(or([" ^ string_of_clause head ^ "])), \n" ^
                                   string_of_s_clausesAux tail
    ;;
let string_of_s_clauses clauses =  string_of_s_clausesAux clauses;;
(* eventuality clause set to string *)
let rec string_of_e_clausesAux = function
    | [] -> ""
    | head::[]  -> "always(or([" ^ string_of_clause head ^ "]))"
    | head::tail  -> "always(or([" ^ string_of_clause head ^ "])), \n" ^
                                   string_of_e_clausesAux tail
    ;;
let string_of_e_clauses clauses =  string_of_e_clausesAux clauses;;


(******************************************************************)
(*              FORMULA STRUCTURAL PROPERTIES                     *)
(******************************************************************)

(* Is a formula atomic? *)
let isAtom atom = match atom with
   | Atom(_) -> true
   | _ -> false
   ;;

(* Is a formula a literal *)
let isLiteral literal = match literal with
   | Literal(_) -> true
   | _ -> false
   ;;

let isTemporalLiteral literal = match literal with
   | Literal(_) -> true
   | Next(Literal(_)) -> true
   | _ -> false
   ;;

(* Returns true if a formula is a truth constant, literal, or a disjunction of literals  *)
let rec isDisjunctive form =
   if (isLiteral form ) then true
   else match form with
   | True -> true
   | False -> true
   | Or(f, g) when ((isDisjunctive f) && (isDisjunctive g))
      -> true
   | Forall(v,x) -> isDisjunctive x
   | Exists(v,x) -> isDisjunctive x
   | _ -> false
   ;;


(* Does the formula start with a temporal operator? *)
let isTemporal formula = match formula with
   | Always(_) -> true
   | AlwaysP(_) -> true
   | Sometime(_) -> true
   | SometimeP(_) -> true
   | Next(_) -> true
   | Until(_,_) -> true
   | Unless(_,_) -> true
   | _ -> false
   ;;

(* True, if the formula does not contain temporal operators *)
let rec isTemporalFree formula =
  (*debug ("isTemporalFree " ^ (string_of_formula formula));*)
  if isTemporal formula
  then ( (*(debug "isTempralFree: returning False1");*) false)
  else match formula with
   | Not x  -> isTemporalFree x
   | And(x,y) -> (isTemporalFree x && isTemporalFree y)
   | Or(x,y) -> (isTemporalFree x && isTemporalFree y)
   | Implies(x,y) -> (isTemporalFree x && isTemporalFree y)
   | Forall(v,x)  -> isTemporalFree x
   | Exists (v,x) -> isTemporalFree x
   | _ -> (*(debug "isTempralFree: returning True");*) true (* True/False *)
   ;;

(* Ordering on formulas (used in simplifications) *)
let myLess (f:formula) (g:formula) =  match (f,g) with
    | (Literal(Atom(a1, vlist1)),Literal(Atom(a2, vlist2))) ->
         Atom(a1, vlist1) < Atom(a2, vlist2)
    | (Literal(Atom(a1, vlist1)),Literal(NotAtom(a2, vlist2))) ->
         Atom(a1, vlist1) < Atom(a2, vlist2)
    | (Literal(NotAtom(a1, vlist1)),Literal(Atom(a2, vlist2))) ->
         Atom(a1, vlist1) < Atom(a2, vlist2)
    | (Literal(NotAtom(a1, vlist1)),Literal(NotAtom(a2, vlist2))) ->
         Atom(a1, vlist1) < Atom(a2, vlist2)
    | (f,g) -> f < g
    ;;

(******************************************************************)
(*              EXTRACT AND TRANSFORM SUB-ELEMNTS                 *)
(******************************************************************)

(* select variables from a list of arguments *)
let rec getVars = function
  | Variable(x)::tail -> x::(getVars tail)
  | _::tail -> (getVars tail)
  | [] -> []
  ;;

(* select variables from a list of arguments *)
let rec getConsts = function
  | Constant(x)::tail -> x::(getConsts tail)
  | _::tail -> (getConsts tail)
  | [] -> []
  ;;

(* free variables of a formula *)
let rec process formula fn  =
  match formula with
  | (True | False) -> []
  | Literal(Atom(_,v)) -> (fn v)
  | Literal(NotAtom(_,v)) -> (fn v)
  | And(f,g) -> union (process f fn) (process g fn)
  | Or(f,g) -> union (process f fn) (process g fn)
  | Implies(f,g) -> union (process f fn) (process g fn)
  | Not(f) -> (process f fn)
  | Forall(v, f) -> exceptL v (process f fn)
  | Exists(v, f) -> exceptL v (process f fn)
  | Always(f) -> process f fn
  | Sometime(f) -> process f fn
  | AlwaysP(f) -> process f fn
  | SometimeP(f) -> process f fn
  | Next(f) -> process f fn
  | Until(f, g) -> union (process f fn) (process g fn)
  | Unless(f, g) -> union (process f fn) (process g fn)
  ;;

let freeVars formula = process formula getVars;;
let constsOf formula = process formula getConsts;;

(* Variable to argument transformation *)
let var2arg = function
   x -> Variable(x);;

let rec  varl2argl = function
   | x::tail -> (var2arg x)::(varl2argl tail)
   | [] -> []
   ;;

(* Returns the list of all atoms occuring in the formula *)
let rec getAtoms formula  =
  match formula with
  | (True | False) -> []
  | Literal(Atom(a,v)) -> [Literal(Atom(a,v))]
  | Literal(NotAtom(a,v)) -> [Literal(Atom(a,v))]
  | And(f,g) -> union (getAtoms f) (getAtoms g)
  | Or(f,g) -> union (getAtoms f) (getAtoms g)
  | Implies(f,g) -> union (getAtoms f) (getAtoms g)
  | Not(f) -> (getAtoms f)
  | Forall(v, f) -> (getAtoms f)
  | Exists(v, f) -> (getAtoms f)
  | Always(f) -> (getAtoms f)
  | Sometime(f) -> (getAtoms f)
  | AlwaysP(f) -> (getAtoms f)
  | SometimeP(f) -> (getAtoms f)
  | Next(f) -> (getAtoms f)
  | Until(f, g) -> union (getAtoms f) (getAtoms g)
  | Unless(f, g) -> union (getAtoms f) (getAtoms g)
  ;;


(******************************************************************)
(*              NEGATION NORMAL FORM TRANSFORMATIONS              *)
(******************************************************************)

let rec nnf = function
  | True -> True
  | False -> False
  | Literal(l) -> Literal(l)
  | And(f,g) -> And (nnf f, nnf g)
  | Or(f,g) -> Or(nnf f,nnf g)
  | Implies(f,g) -> Or(negate f, nnf g)
  | Not(f) -> negate f
  | Forall(v,f) -> Forall(v, nnf f)
  | Exists(v,f) -> Exists(v, nnf f)
  | Always(f) -> Always(nnf f)
  | Sometime(f) -> Sometime(nnf f)
  | AlwaysP(f) -> AlwaysP(nnf f)
  | SometimeP(f) -> SometimeP(nnf f)
  | Next(f) -> Next(nnf f)
  | Until(f,g) -> Until(nnf f, nnf g)
  | Unless(f,g) -> Unless(nnf f, nnf g)
and
   negate form = debug("negate called: " ^ (string_of_formula form)); match form with
  | True -> False
  | False -> True
  | Literal(l) ->
     begin
      match l with
      | Atom(a,v) -> Literal(NotAtom(a,v))
      | NotAtom(a,v) -> Literal(Atom(a,v))
     end
  | And(f,g) -> Or (negate f, negate g)
  | Or(f,g) -> And(negate f,negate g)
  | Implies(f,g) -> And(nnf f, negate g)
  | Not(f) -> nnf f
  | Forall(v,f) -> Exists (v, negate f)
  | Exists(v,f) -> Forall (v, negate f)
  | Always(f) -> Sometime(negate f)
  | Sometime(f) -> Always(negate f)
  | AlwaysP(f) -> SometimeP(negate f)
  | SometimeP(f) -> AlwaysP(negate f)
  | Next(f) -> Next(negate f)
  | Until(f,g) -> debug("f = "^(string_of_formula f) ^ "   g = " ^ (string_of_formula g)); Unless(negate g,And(negate f, negate g))
  | Unless(f,g) -> Until(negate g, And(negate f, negate g))
 ;;


(******************************************************************)
(*               SIMPLIFICATION OF THE FORMULA IN NNF             *)
(******************************************************************)

(* Apply one simplification step *)
let rec elementarySimplify form = debug ("elementarySimplify called with " ^(string_of_formula form));
match form with
    (* Jenssen simplifications *)
    | Not(False) -> debug "1 ";
   	    True
    | Not(True)   -> debug "2 ";
 	    False
    | Next(False) -> debug "3 ";
 	    False
    | Next(True)  -> debug "4 ";
 	    True
    | Sometime(False) -> debug "5 ";
 	    False
    | Sometime(True) -> debug "6 ";
 	    True
    | Always(False) -> debug "7 ";
 	    False
    | Always(True) -> debug "8 ";
 	    True
    | Forall(_, True) -> debug "75";
        True
    | Forall(_, False) -> debug "76";
        False
    | Exists(_, True) -> debug "77";
        True
    | Exists(_, False) -> debug "78";
        False
    (*| Sometime(Next(f)) -> debug " ";
 Next(Sometime(f)) -- same number of clauses*)
    | Sometime(Sometime(f)) -> debug "9 ";
 	    Sometime(elementarySimplify f)
    | Sometime(Always(Sometime(f))) -> debug "10 ";
 	    Always(Sometime(elementarySimplify f))
    | Sometime(Until(f,g)) -> debug "11 ";
 	    Sometime(elementarySimplify g)
    (*| Always(Next(f)) -> debug " ";
 Next(Always(f)) -- same number of clauses *)
    | Always(Always(f)) -> debug "12 ";
 	    Always(elementarySimplify f)
    | Always(Sometime(Always(f))) -> debug "13 ";
 	    Sometime(Always(elementarySimplify f))
     (*changed from Until to Unless!!!*)
    | Always(Unless(f,g)) -> debug "14 ";
 	    Always(Or((elementarySimplify f), (elementarySimplify g)))
    (* *)
    | Until(False, f) -> debug "15 ";
 	    elementarySimplify f
    | Until(f, False) -> debug "16 ";
 	    False
    | Until(True, f) -> debug "17 ";
 	    Sometime(elementarySimplify f)
    | Until(f, True) -> debug "18 ";
 	    True
    | Until(Next(f), Next(g)) -> debug ("19: "); debug((string_of_formula f) ^ " : " ^ (string_of_formula g));
 	    Next(Until((elementarySimplify f), (elementarySimplify g))) (* one clause gained *)
    | Until(f, Sometime(g)) -> debug "20 ";
 	    Sometime(elementarySimplify g)
    | Until(p, q) when debug("c1"); ((isTemporalLiteral p )&& (isTemporalLiteral q) && (p=(negate q))) -> debug ("21 : p = "); debug((string_of_formula p) ^ " : q = " ^ (string_of_formula q));
	    Sometime(elementarySimplify q)
(*
    | Until(p, q) when q=(negate p) -> debug "22 ";
 	    Sometime(p)
*)
    | Until(f,g) when f=g -> debug "23 ";
 	    elementarySimplify f
    | Unless(False, f) -> debug "24 ";
 	    elementarySimplify f
    | Unless(f, False) -> debug "25 ";
 	    Always(elementarySimplify f)
    | Unless(True, f) -> debug "26 ";
 	    True
    | Unless(f, True) -> debug "27 ";
 	    True
    | Unless(Next(f), Next(g)) -> debug "28 ";
 	    Next(Unless((elementarySimplify f), (elementarySimplify g))) (* one clause gained *)
    | Unless(Always(f), g) -> debug "29 ";
 	    Or((Always(elementarySimplify f)), ((elementarySimplify g)))
    | Unless(p, q) when ((isTemporalLiteral p )&& (isTemporalLiteral q) && p=(negate q)) -> debug "30 ";
 	    True
(*
    | Unless(p, q) when q=(negate p) -> debug "31 ";
 	True
*)
    | Unless(f,g) when f=g -> debug "32 ";
 	    elementarySimplify f
    (* *)
    | And(False, f) -> debug "33 ";
 	    False
    | And(True, f) -> debug "34 ";
 	    elementarySimplify f
    | And(f, False) -> debug "35 ";
 	    False
    | And(f, True) -> debug "36 ";
  	    elementarySimplify f
    | And(Next(f), Next(g)) -> debug "37 ";
 	    Next(And((elementarySimplify f), (elementarySimplify g))) (* 2 clauses gained *)
    | And(Always(f), Always(g)) -> debug "38 ";
 	    Always(And((elementarySimplify f), (elementarySimplify g))) (* 2 clauses gained *)
    | And(p, q) when p=q -> debug "39 ";
  	    elementarySimplify p
    | And(p, q) when p=(negate q) -> debug "40 ";
  	    False
    | And(p, q) when q=(negate p) -> debug "41 ";
  	    False
    | Or(False, f) -> debug "42 ";
 	    elementarySimplify f
    | Or(True, f) -> debug "43 ";
 	    True
    | Or(f, False) -> debug "44 ";
 	    elementarySimplify f
    | Or(f, True) -> debug "45 ";
 	    True
    | Or(Next(f), Next(g)) -> debug "46 ";
 	    Next(Or((elementarySimplify f),(elementarySimplify g))) (* 2 clauses gained *)
    | Or(Sometime(f), Sometime(g)) -> debug "47 ";
 	    Sometime(Or((elementarySimplify f), (elementarySimplify g))) (* 2 clauses gained*)
    | Or(p, q) when p=q -> debug "48 ";
 	    elementarySimplify p
    | Or(p, q) when p=(negate q) -> debug "49 ";
 	    True
    | Or(p, q) when q=(negate p) -> debug "50 ";
 	    True
    (* Trying to "normalise" subformulae *)
    | And(f,g) when
        ((match g with And(_,_) -> false | _ -> true )&&
	 (myLess g f))
	-> debug ("51 : AND : "); debug ((string_of_formula f ) ^ " : " ^ (string_of_formula g));
  	    And(elementarySimplify g, elementarySimplify f)
    | Or(f,g) when
        ((match g with Or(_,_) -> false | _ -> true )&&
	 (myLess g f))
	-> debug "52 ";
  	    Or(elementarySimplify g, elementarySimplify f)
    | And(And(f,g), h) -> debug "53 ";
 	    And(elementarySimplify f, And(elementarySimplify g, elementarySimplify h))
    | Or(Or(f,g), h) -> debug "54 ";
 	    Or(elementarySimplify f, Or(elementarySimplify g,elementarySimplify h))
    | And(f, And(g,h)) when (myLess g f) -> debug "55 ";
 	    And(elementarySimplify g, And(elementarySimplify f,elementarySimplify h))
    | Or(f, Or(g,h)) when (myLess g f) -> debug "56 ";
 	    Or(elementarySimplify g, Or(elementarySimplify f, elementarySimplify h))
    (* *)
    | And(p, And(q,r)) when p=q -> debug "57 ";
  	    And(elementarySimplify p,elementarySimplify r)
    | And(p, And(q,r)) when p=(negate q) -> debug "58 ";
  	    False
    | And(p, And(q,r)) when q=(negate p) -> debug "59 ";
  	    False
    | Or(p, Or(q,r)) when p=q -> debug "60 ";
  	    Or(elementarySimplify p,elementarySimplify r)
    | Or(p, Or(q,r)) when p=(negate q) -> debug "61 ";
  	    True
    | Or(p, Or(q,r)) when q=(negate p) -> debug "62 ";
  	    True
    (* none of the above worked *)
    (* go  inside *)
    | And(f,g) -> debug "63 ";
 	    And(elementarySimplify f, elementarySimplify g)
    | Or(f,g) -> debug "64 ";
 	    Or(elementarySimplify f, elementarySimplify g)
    | Implies(f,g) -> debug "65 ";
 	    Implies(elementarySimplify f, elementarySimplify g)
    | Not(f) -> debug "66 ";
 	    Not(elementarySimplify f)
    | Forall(v, f) -> debug "67 ";
 	    Forall(v, elementarySimplify f)
    | Exists(v, f) -> debug "68 ";
 	    Exists(v, elementarySimplify f)
    | Always(f) -> debug "69 ";
 	    Always(elementarySimplify f)
    | Sometime(f) -> debug "70 ";
 	    Sometime(elementarySimplify f)
    | Next(f) -> debug ("71 : "); debug((string_of_formula f));
 	    Next(elementarySimplify f)
    | Until(f,g) -> debug ("72 : UNTIL : "); debug((string_of_formula f) ^ " : " ^ (string_of_formula g));
 	    Until(elementarySimplify f, elementarySimplify g)
    | Unless(f,g) -> debug ("73 : "); debug((string_of_formula f) ^ " : " ^  (string_of_formula g));
 	    Unless(elementarySimplify f,elementarySimplify g)
    (* constants True/False*)
    | x -> debug ("74 : "); debug((string_of_formula x));
 	    x
    ;;

(* Apply simplification steps while possible *)
let simplify (form:formula) (channel:out_channel) (isVerbose:bool) =
   debug("simplify " ^ (string_of_formula form));
   let tmpform = ref form
   and tmpsimp = ref (elementarySimplify form)
   in
   while (!tmpform <> !tmpsimp)
   do
   if (isVerbose=true) then begin
       output_string channel ("simplified to: " ^ string_of_formula !tmpsimp); print_newline () end;
     tmpform := !tmpsimp;
     tmpsimp := elementarySimplify !tmpform
   done ; !tmpform
;;

(******************************************************************)
(*                    NEW NAMES GENERATION                        *)
(******************************************************************)
let count = ref 0;;
(*let newNamesList = ref [];;*)
let newVar name = incr count ; name ^  (string_of_int !count);;
let resetVar = count :=0;;

let newSkolem () = newVar "skolem";;

let newLiteral varlist =
    let tmpLit = Literal(Atom(newVar "NVV", (varl2argl varlist)))
  in (*newNamesList:=tmpLit::(!newNamesList);*) tmpLit
  ;;

(******************************************************************)
(*                    SMART RENAMING                              *)
(******************************************************************)
(* The following functions are used to prevent the same subformulae *)
(* To be named differently *)
(* A list to keep all renamed formulas *)
let seenList = ref (List.tl [(True,True)]);;

(* already seen, get the name *)
let isSeen (form:formula) = List.mem_assoc form !seenList;;

(* set the name (when rename) *)
let setSeen (form:formula) (name:formula) = seenList := (form, name)::!seenList;;

let getSeen (form:formula) = List.assoc form !seenList

(* returns the formula representing the result of renaming formula with *)
(* proposition: \always\forall (proposition => formula) *)
let rename proposition formula =
    assert((freeVars proposition) = (freeVars formula));
    if List.length (freeVars formula) = 0
    then
    Always(Or(negate (proposition), formula))
    else
    Always(Forall(freeVars formula, Or(negate (proposition), formula)))
   ;;


(******************************************************************)
(*              DSNF TRANSFORMATIONS                              *)
(******************************************************************)

(* the useFOrenaming argument controls how fo formulas are processed:
if false, then by de Morgan laws, by renaming else*)

(*
(* Transformation to CNF by renaming *)
(* form is supposed to be in NNF *)
let rec foToCNFbyRenaming form =
  (*print_string ("FOrenaming " ^ (string_of_formula form) ^ "\n\n"); flush stdout;*)
  if (isSeen form)
  then (getSeen form,[],[],[])
  else
  if isDisjunctive form
  then
    (form,[],[],[])
  else
  match form with
    | And(f, g) ->
      let (iP1, uP1, sP1, eP1) = foToCNFbyRenaming f
      and (iP2, uP2, sP2, eP2) = foToCNFbyRenaming g
      in
       (And(iP1, iP2), (union uP1 uP2), [], [] )
    | Or(f, g) when ((isLiteral f) || (isLiteral g)) ->
      let (iP1, uP1, sP1, eP1) = foToCNFbyRenaming f
      and (iP2, uP2, sP2, eP2) = foToCNFbyRenaming g
      in
       (Or(iP1, iP2), (union uP1 uP2), [], [])
    | Or(f, g) (* both are non-litarls *) ->
       let newP = newLiteral (freeVars f)
       and (iP1, uP1, sP1, eP1) = foToCNFbyRenaming f
       in setSeen iP1 newP ;
       let (iP2, uP2, sP2, eP2) = foToCNFbyRenaming g
       in
       (Or(newP, iP2),
         (rename newP iP1)::(union uP1 uP2),
	 [], [])
    | Forall(v,y) ->
        let (iP,uP,sP,eP) = foToCNFbyRenaming y
        in (Forall(v, iP), uP,sP,eP)
    | Exists(v,y) ->
        let (iP,uP,sP,eP) = foToCNFbyRenaming y
        in (Exists(v, iP), uP,sP,eP)
    | _ -> raise Illegal6
    ;;

(* Choose how to proceed a fo-formula *)
let fodsnfselect form =
  if not !useFOrenaming
  then (form,[],[],[]) (* will be transformed to CNF by de Morgan rules *)
  else
    foToCNFbyRenaming form (* do transformation by renaming*)
  ;;*)

(* Returns DSNF represented as: formula * uList * sList *eList *)
(*                                iP       uP      sP     eP   *)
(*                                                             *)
(* ASSUME that formula is in NNF                               *)
let rec dsnfWrap ~useFOrenaming form =
    debug ("dsnfWrap input: " ^ (string_of_formula form));
    match form with
     | f when (isTemporalFree f) -> (f, [], [], [])
     | And(x,y) ->
         let (iP1, uP1,sP1,eP1) = dsnfWrap ~useFOrenaming x
         and (iP2, uP2,sP2,eP2) = dsnfWrap ~useFOrenaming y
         in (And(iP1, iP2), union uP1 uP2, union sP1 sP2, union eP1 eP2)
     | Always (f) when (isTemporalFree f) ->
        (True, [f], [], [])

(* a special treatment for step clauses in the input *)
     | Always(Or(lhs,rhs)) when
          ((isTemporalLiteral lhs) && (isTemporalLiteral rhs)) ->
                 (True, [], [Always(Or(lhs,rhs))], [])
     | Always(Forall(_, (Or(lhs,rhs)))) when
          ((isTemporalLiteral lhs) && (isTemporalLiteral rhs)) ->
                 (True, [], [Always(Or(lhs,rhs))], [])

(* else use the standard transformations *)
     | _ -> dsnf ~useFOrenaming form

and dsnf ~useFOrenaming form =
    debug ("dsnf input: " ^ (string_of_formula form));
  (*  if isTemporalFree form *)
  (*  then fodsnfselect form *)
  (*  else                   *)
    if (isSeen form)
    then (getSeen form,[],[],[])
    else
    if isDisjunctive form (* it is also temporal free in this case *)
    then
      (form,[],[],[])
    else
    match form with
     (* booleans go first *)
     | Not x  ->
         let (iP,uP,sP,eP) = dsnf ~useFOrenaming x
         in (Not(iP), uP,sP,eP)
     | And(x,y) ->
         let (iP1, uP1,sP1,eP1) = dsnf ~useFOrenaming x
         and (iP2, uP2,sP2,eP2) = dsnf ~useFOrenaming y
         in (And(iP1, iP2), union uP1 uP2, union sP1 sP2, union eP1 eP2)
  (*   | Or(x,y) ->
         let (iP1, uP1,sP1,eP1) = dsnf ~useFOrenaming x
         and (iP2, uP2,sP2,eP2) = dsnf ~useFOrenaming y
         in (Or(iP1, iP2), union uP1 uP2, union sP1 sP2, union eP1 eP2)*)
      | Or(f, g) when ((not useFOrenaming) || (isLiteral f) || (isLiteral g)) ->
        let (iP1, uP1, sP1, eP1) = dsnf ~useFOrenaming f
        and (iP2, uP2, sP2, eP2) = dsnf ~useFOrenaming g
        in
         (Or(iP1, iP2), (union uP1 uP2), (union sP1 sP2), (union eP1 eP2))
      | Or(f, g) when (useFOrenaming) (* both are non-litarls & useFOrenaming *) ->
         let newP = newLiteral (freeVars f)
         and (iP1, uP1, sP1, eP1) = dsnf ~useFOrenaming f
         in setSeen iP1 newP ;
         let (iP2, uP2, sP2, eP2) = dsnf ~useFOrenaming g
         in
         (Or(newP, iP2),
           (rename newP iP1)::(union uP1 uP2), (union sP1 sP2), (union eP1 eP2))
     | Implies(x,y) ->
         raise Illegal7
         (*let (iP1, uP1,sP1,eP1) = dsnf x
         and (iP2, uP2,sP2,eP2) = dsnf y
         in (Implies(iP1, iP2), union uP1 uP2, union sP1 sP2, union eP1 eP2)*)
     (* Quantifiers *)
     | Forall(v,y) ->
         let (iP,uP,sP,eP) = dsnf ~useFOrenaming y
         in (Forall(v, iP), uP,sP,eP)
     | Exists(v,y) ->
         let (iP,uP,sP,eP) = dsnf ~useFOrenaming y
         in (Exists(v, iP), uP,sP,eP)
     (* Temporal operators *)
     | Always(f) ->
         let newP = newLiteral (freeVars f)
          and (iP,uP,sP,eP) = dsnf ~useFOrenaming f
         in setSeen (Always(f)) newP ;
         (newP,
           (rename newP iP)::uP,
  	 (rename newP (Next(newP)))::sP,
  	 eP
         )
     | Next(f) ->
         let newP = newLiteral (freeVars f)
         and newQ =
           (
             if (isLiteral f) then f
              else (newLiteral (freeVars f))
           )
          and (iP,uP,sP,eP) = dsnf ~useFOrenaming f
         in setSeen (Next (f)) newP ;
         (newP,
           (if (isLiteral f) then uP else
            (rename newQ iP)::uP),
  	  (rename newP (Next(newQ)))::sP,
  	  eP
         )
     | Sometime(f) ->
         let newP = newLiteral (freeVars f)
         and newQ = newLiteral (freeVars f)
          and (iP,uP,sP,eP) = dsnf ~useFOrenaming f
         in setSeen (Sometime(f)) newP ;
         (newP,
            (rename newQ iP)::uP,
            sP,
  	  (rename newP (Sometime(newQ)))::eP
         )
     | Until(f,g) ->
         if not (isLiteral f)
         then
           let newP = newLiteral (freeVars (Until(f,g)))
  	 in let (iP,uP,sP,eP) = dsnf ~useFOrenaming (Until(newP, g))
  	    and (iP2,uP2,sP2,eP2) = dsnf ~useFOrenaming (f)
  	 in (iP,
  	 (rename newP iP2)::(uP@uP2),
  	 sP@sP2, eP@eP2)
         else if not (isLiteral g)
         then
           let newQ = newLiteral (freeVars (Until(f,g)))
  	 in let (iP,uP,sP,eP) = dsnf ~useFOrenaming (Until(f, newQ))
  	    and (iP2,uP2,sP2,eP2) = dsnf ~useFOrenaming (g)
  	 in (iP,
  	 (rename newQ iP2)::(uP@uP2),
  	 sP@sP2, eP@eP2)
         else (* Both f and g are atoms *)
           let newP = newLiteral (freeVars (Until(f,g)))
           and newQ = newLiteral (freeVars (Until(f,g)))
           and (iP1,uP1,sP1,eP1) = dsnf ~useFOrenaming f
           and (iP2,uP2,sP2,eP2) = dsnf ~useFOrenaming g
           in setSeen (Until(f,g)) newP ;
  	 (newP,
  	   (
  	     (rename newP (Or(f,g)))::
  	     (rename newP (Or(g,newQ)))::[]
  	   ) @ (union uP1 uP2),
  	   (
  	     (rename newQ (Next(Or(f, g))))::
  	     (rename newQ (Next(Or(newQ, g))))::[]
  	   ) @ (union sP1 sP2),
  	   (rename newP (Sometime g))::(union eP1 eP2)
  	 )
     | Unless(f,g) ->  (* same as until but without the eventuality. cut-n-paste *)
         if not (isLiteral f)
         then
           let newP = newLiteral (freeVars (Unless(f,g)))
  	 in let (iP,uP,sP,eP) = dsnf ~useFOrenaming (Unless(newP, g))
  	    and (iP2,uP2,sP2,eP2) = dsnf ~useFOrenaming (f)
  	 in (iP,
  	 (rename newP iP2)::(uP@uP2),
  	 sP@sP2,eP@eP2)
         else if not (isLiteral g)
         then
           let newQ = newLiteral (freeVars (Unless(f,g)))
  	 in let (iP,uP,sP,eP) = dsnf ~useFOrenaming (Unless(f, newQ))
  	    and (iP2,uP2,sP2,eP2) = dsnf ~useFOrenaming (g)
  	 in (iP,
  	 (rename newQ iP2)::(uP@uP2),
  	 sP@sP2,eP@eP2)
         else (* Both f and g are atoms *)
           let newP = newLiteral (freeVars (Unless(f,g)))
           and newQ = newLiteral (freeVars (Unless(f,g)))
           and (iP1,uP1,sP1,eP1) = dsnf ~useFOrenaming f
           and (iP2,uP2,sP2,eP2) = dsnf ~useFOrenaming g
           in setSeen (Unless(f,g)) newP ;
  	 (newP,
  	   (
  	     (rename newP (Or(f,g)))::
  	     (rename newP (Or(g,newQ)))::[]
  	   ) @ (union uP1 uP2),
  	   (
  	     (rename newQ (Next(Or(f, g))))::
  	     (rename newQ (Next(Or(newQ, g))))::[]
  	   ) @(union sP1 sP2),
  	   (union eP1 eP2)
  	 )
         | _ -> raise Illegal1
;;



(******************************************************************)
(*                 QUANTIFIER ELIMINATION                         *)
(******************************************************************)

(* Substitute in the argument list the variable var with sk *)
let rec substL alist var sk = match alist with
    | v::tail when v=var -> sk::substL tail var sk
    | x::tail -> x::substL tail var sk
    | [] -> []
    ;;

(* Substitute in f the argument var with sk *)
let rec subst f var sk = match f with
    | True -> True
    | False -> False
    | And(f,g) -> And(subst f var sk, subst g var sk)
    | Or(f,g) -> Or(subst f var sk, subst g var sk)
    | Implies(f,g) -> Implies(subst f var sk, subst g var sk)
    | Not(f) -> Not(subst f var sk)
    | Forall(v,f) -> Forall(v, subst f var sk)
    | Exists(v,f) -> Exists(v, subst f var sk)
    | Always(f) -> Always(subst f var sk)
    | Sometime(f) -> Sometime(subst f var sk)
    | AlwaysP(f) -> AlwaysP(subst f var sk)
    | SometimeP(f) -> SometimeP(subst f var sk)
    | Next(f) -> Next(subst f var sk)
    | Until(f,g) -> Until(subst f var sk, subst g var sk)
    | Unless(f,g) -> Unless(subst f var sk, subst g var sk)
    (* the interesting part *)
    | Literal(Atom(a, vlist)) -> Literal(Atom(a, substL vlist var sk))
    | Literal(NotAtom(a, vlist)) -> Literal(NotAtom(a, substL vlist var sk))
    ;;

let rec introduceSkolem existentialVars form freevars =
 match existentialVars with
    | v::tail -> let ns = Skolem(newSkolem(), freevars)
                 in subst (introduceSkolem tail form freevars) (var2arg v) ns
    | [] -> form
    ;;

(* Skolemise existential and remove universal quantifiers *)
(* Pre-requirements: form is in NNF *)
let rec eliminateQ form freevars = match form with
    | True -> True
    | False -> False
    | Literal(l) -> Literal(l)
    | And(f,g) -> And(eliminateQ f freevars, eliminateQ g freevars)
    | Or(f,g) -> Or(eliminateQ f freevars, eliminateQ g freevars)
    | Forall(v,f) -> eliminateQ f (union v freevars)
    (* the interesting part *)
    | Exists(v,f) -> introduceSkolem v (eliminateQ f freevars) freevars
    (* This does not have any logical meaning, but see TIME paper for
       justification *)
    | Next(f) -> Next(eliminateQ f freevars)
    | Sometime(f) -> Sometime(eliminateQ f freevars)
    | Always(f) -> Always(eliminateQ f freevars)
    (* No Not, Implies and temporal operators here! *)
    | _ -> print_string ("trouble = "^(string_of_formula form)) ; flush stdout; raise Illegal2
    ;;

(* Polymorphism *)
let eliminateQ form = eliminateQ form [] ;;

(* the same for a list of formulas *)
let rec eliminateQl = function
    | head::tail -> (eliminateQ head)::(eliminateQl tail)
    | [] -> []
    ;;

(******************************************************************)
(*                 CONJUNCTIVE NORMAL FORM TRANSFORMATION         *)
(******************************************************************)

(* conjective normal form (Using de-Morgan laws) *)
let rec cnf = function
    | Or(f,g)  -> cnfAux (Or(cnf f, cnf g))
    | And(f,g) -> And(cnf f, cnf g)
    (* a hack -- Always can only be the leading connective *)
    | Always(f) -> Always(cnf f)
    | x -> x
and cnfAux = function
    | Or(f, And(g,h)) -> And(cnfAux (Or(f, g)), cnfAux (Or(f, h)))
    | Or(And(f,g), h) -> And(cnfAux (Or(f, h)), cnfAux (Or(g, h)))
    | x -> x
    ;;

(* same for a list of formulas*)
let rec cnfl = function
    | head::tail -> (cnf head)::(cnfl tail)
    | [] -> []
    ;;
(******************************************************************)
(*                 CNF -> LIST OF CLAUSES                         *)
(******************************************************************)
(* CNF to a list of clauses *)
let rec clausify = function
    | Always(f) -> clausify f
    | And(f,g) -> union (clausify f) (clausify g)
    | Or(f,g) ->  [clausifyAux (Or(f,g))]
    | True -> []
    | False -> [[]]
    | Literal(l) -> [[Literal(l)]]
    | _ -> raise Illegal3
and clausifyAux = function
    | Next(f) -> clausifyAux2 f
    | Or(f,g) -> union (clausifyAux f) (clausifyAux g)
    | x  -> [x]
and clausifyAux2 = function
    | Or(f,g) -> union (clausifyAux2 f) (clausifyAux2 g)
    | x -> [Next(x)]
    ;;

(* same for a list of formulas*)
let rec clausifyl = function
    | head::tail -> union (clausify head) (clausifyl tail)
    | [] -> []
    ;;



(******************************************************************)
(*                 CONSTANT FLOODING (IN ALL SENCES)              *)
(******************************************************************)

(* abuse of skolem. Let's see if it works *)
let hidden var =  Skolem("hidden", [var]) ;;
let const var = Skolem("constant", [var]) ;;

(* Given a step clause of the form P(x) => \next Q(x) returns a list of *)
(* two clauses                                                          *)
(* P(x) => \next Q(hidden(x)) and P(const(x)) => \next Q(const(x)       *)
let foStepClause clause =
 debug ("foStepClause clause = " ^ (string_of_formula clause));
 match clause with
  | Always(Or(lhs,rhs)) ->
   let varlist = freeVars clause
   in
   (* monodicity check *)
   if List.length varlist > 1 then raise NonMonodic
   else begin
     if List.length varlist = 1 then
     begin
       let varname = List.hd varlist
       in let var = Variable(varname)
       in Always(Or(lhs, (subst rhs var (hidden varname) )))::subst clause var (const varname)::[]
     end
     else [clause]
   end
 | _ -> raise Illegal4
;;

let rec foStepClauses = function
  | [] -> []
  | head::tail -> (foStepClause head)@(foStepClauses tail)
  ;;

let processFOconstant form constantName =
let cnew = const constantName
and cold = Constant(constantName)
in
subst form cold cnew ;;

let rec processFOconstantsAux form constantList =
match constantList with
    | head::tail ->let newf = (processFOconstant form head) in
        processFOconstantsAux newf tail
    | [] -> form
    ;;

let processFOconstants form =
  let clist = constsOf form in
  let newf = processFOconstantsAux form clist
  in newf
   ;;

let rec processFOconstantsl = function
    | head::tail -> (processFOconstants head)::(processFOconstantsl tail)
    | [] -> []

(* Constant flooding *)
let rec flood formList constList = match formList with
    | head::tail -> [head]@(floodAux head constList)@(flood tail constList)
    | [] -> []
and
    floodAux form constList = match constList with
    | head::tail -> (floodAux2 form head)@(floodAux form tail)
    | [] -> []
and
    floodAux2 form const = match form with
    | Always(Or(_,_)) ->  []
    | Always(Forall(v, f)) ->  assert (List.length v = 1); [Always(subst f ( var2arg (List.hd v) ) (Constant(const)))]
    | _ -> raise Illegal5
    ;;
