(* This code derives from a GPL'ed code and so is GPL'ed *)


open Fotypes;;
open Fofunctions;;


let verbose = ref false;;
let useSimplification = ref false;;
let filename = ref "";;
let inx = ref stdin;;
let outx = ref stdout;;
let atoms = ref false;;
let useFOrenaming = ref false;;

(*let resetVerbose = verbose := false;;*)

let setInFilename name = inx := open_in name;;
let setOutFilename name = outx := open_out name;;

let args_spec = ("-v", Arg.Set verbose, "Be verbose (print intermediate transformations).")::
                ("-s", Arg.Set useSimplification, "Use simplifications.")::
		("-r", Arg.Set useFOrenaming, "Transform to CNF by renaming")::
                (*("-fo", Arg.Set fo, "Perform transformation for FO (expanding domains).")::*)
                ("-al", Arg.Set atoms, "Include the 'order' statement with the list of all atoms in the input formula (experimental feature).")::
                ("-i", Arg.String setInFilename,
		  "Specify the input file. If not given, stdin is used.")::
                ("-o", Arg.String setOutFilename,
		  "Specify the output file. If not given, stdout is used.")::
		[];;

let usage_spec = "Usage: translate [-v] [-s] [-i infile] [-o outfile]";;

let anonfun astring = Arg.usage args_spec usage_spec; exit 0;;

(* main function *)
let _ =
  try
    (*print_string ( Filename.basename Sys.argv.(0) );*)
    let fo = String.starts_with ~prefix:"fo" (Filename.basename Sys.argv.(0)) in
    Arg.parse args_spec anonfun usage_spec ;
    let lexbuf = Lexing.from_channel !inx in
      let result = Foyacc.start Folex.lexer lexbuf in
        let constList = constsOf result in
	if !atoms=true then begin
	  let atomList = getAtoms result in
	    output_string !outx ("order(" ^ (string_of_clause atomList) ^ ").\n");
	end;
        if !verbose=true then begin
	   output_string !outx ("Input: " ^ string_of_formula result^"\n");
	   flush !outx
	   end;
        let inNNF = nnf result in
        if !verbose then begin
	  output_string !outx "In NNF: ";
          output_string !outx (string_of_formula inNNF^"\n");
          debug("DONE");
	  flush !outx;
          debug("DONE");
	end;
    debug("done ");
	let simplified =
	if !useSimplification then
	  simplify inNNF !outx !verbose
	else inNNF
        in
        if !verbose then begin
	  output_string !outx "After all simplifications:\n";
          output_string !outx (string_of_formula simplified^"\n");
	  flush !outx
	end;
        let useFOrenaming = !useFOrenaming in
	let (iP,uP,sP,eP) = dsnfWrap ~useFOrenaming simplified in
        if !verbose then begin
	output_string !outx "After transformations, the DSNF is\n";
	output_string !outx "iP = {\n";
        output_string !outx ((string_of_formula iP)^"\n}\n");
	output_string !outx "uP = {\n";
        output_string !outx ((string_of_formulas uP)^"\n}\n");
	output_string !outx "sP = {\n";
        output_string !outx ((string_of_formulas sP)^"\n}\n");
	output_string !outx "eP = {\n";
        output_string !outx ((string_of_formulas eP)^"\n}\n");
	flush !outx
	end;
	(* Skolemization *)
	let skolemisedIP = eliminateQ iP
	and skolemisedUP = eliminateQl uP
	and skolemisedSP = eliminateQl sP
	and skolemisedEP = if fo then (eliminateQl (flood eP constList)) else (eliminateQl eP)
	in
	(* FO transformations *)
	let processedIP = if fo then (processFOconstants skolemisedIP) else skolemisedIP
	and processedUP = if fo then (processFOconstantsl skolemisedUP) else skolemisedUP
	and processedSP = if fo then (foStepClauses skolemisedSP) else skolemisedSP
	and processedEP = if fo then (processFOconstantsl skolemisedEP) else skolemisedEP
	in
	(**)
	let cnfedIP = cnf processedIP
	and cnfedUP = cnfl processedUP
	in
	let clausesIP = clausify cnfedIP
	and clausesUP = clausifyl cnfedUP
	and clausesSP = clausifyl processedSP
	and clausesEP = clausifyl processedEP in
	(* prepare to print *)
	let preamble = "and([\n"
	and ending = "]).\n" in
	let printed = ref true in
	(* translate into strings *)
	let icstringAux = string_of_i_clauses clausesIP
	and ucstringAux = string_of_u_clauses clausesUP
	and scstringAux = string_of_s_clauses clausesSP
	and ecstringAux = string_of_e_clauses clausesEP in
	(* Add commas depending on whether the next string is empty *)
	let icstring = if ((String.length ucstringAux = 0) ||
                   (String.length icstringAux = 0)) then icstringAux
	                                                else icstringAux ^",\n"
	and ucstring = if ((String.length scstringAux = 0) ||
             (((String.length ucstringAux)+(String.length icstringAux)) = 0 ))
                                                    then ucstringAux
	                                                else ucstringAux ^",\n"
	and scstring = if String.length ecstringAux = 0 then scstringAux
	                                                else scstringAux ^",\n"
        (* no comma after ucstring *)
	and ecstring = ecstringAux  in
	(* Collect strings *)
	let resultStr = preamble^icstring^ucstring^scstring^ecstring^ending^"\n" in
	(*print_string (string_of_clause (!newNamesList));*)
	output_string !outx (resultStr); if !outx != stdout then close_out !outx
  with Parsing.Parse_error -> print_endline ("Parse error line " ^
     string_of_int (!Folex.currentLine) ^ " characters " ^
     string_of_int (!Folex.posmin) ^ "-" ^ string_of_int (!Folex.posmax))
     | Sys_error astring ->  print_endline (astring);;
