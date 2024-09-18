(* This code derives from a GPL'ed code and so is GPL'ed *)


open Fotypes;;
open Fofunctions;;


(* main function *)
let main verbose useSimplification useFOrenaming atoms inFilename outFilename =
  try
    (*print_string ( Filename.basename Sys.argv.(0) );*)
    let fo = String.starts_with ~prefix:"fo" (Filename.basename Sys.argv.(0)) in
    let inx =
      match inFilename with
      | None -> stdin
      | Some name -> open_in name
    in
    let outx =
      match outFilename with
      | None -> stdout
      | Some name -> open_out name
    in
    let lexbuf = Lexing.from_channel inx in
      let result = Foyacc.start Folex.lexer lexbuf in
        let constList = constsOf result in
	if atoms then begin
	  let atomList = getAtoms result in
	    output_string outx ("order(" ^ (string_of_clause atomList) ^ ").\n");
	end;
        if verbose then begin
	   output_string outx ("Input: " ^ string_of_formula result^"\n");
	   flush outx
	   end;
        let inNNF = nnf result in
        if verbose then begin
	  output_string outx "In NNF: ";
          output_string outx (string_of_formula inNNF^"\n");
          debug("DONE");
	  flush outx;
          debug("DONE");
	end;
    debug("done ");
	let simplified =
	if useSimplification then
	  simplify inNNF outx verbose
	else inNNF
        in
        if verbose then begin
	  output_string outx "After all simplifications:\n";
          output_string outx (string_of_formula simplified^"\n");
	  flush outx
	end;
	let (iP,uP,sP,eP) = dsnfWrap ~useFOrenaming simplified in
        if verbose then begin
	output_string outx "After transformations, the DSNF is\n";
	output_string outx "iP = {\n";
        output_string outx ((string_of_formula iP)^"\n}\n");
	output_string outx "uP = {\n";
        output_string outx ((string_of_formulas uP)^"\n}\n");
	output_string outx "sP = {\n";
        output_string outx ((string_of_formulas sP)^"\n}\n");
	output_string outx "eP = {\n";
        output_string outx ((string_of_formulas eP)^"\n}\n");
	flush outx
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
	output_string outx (resultStr); if outx != stdout then close_out outx
  with Parsing.Parse_error -> print_endline ("Parse error line " ^
     string_of_int (!Folex.currentLine) ^ " characters " ^
     string_of_int (!Folex.posmin) ^ "-" ^ string_of_int (!Folex.posmax))
     | Sys_error astring ->  print_endline (astring);;

open Cmdliner

let verbose =
  let doc = "Be verbose (print intermediate transformations)." in
  Arg.(value & flag & info ["v"] ~doc)

let useSimplification =
  let doc = "Use simplifications." in
  Arg.(value & flag & info ["s"] ~doc)

let useFOrenaming =
  let doc = "Transform to CNF by renaming." in
  Arg.(value & flag & info ["r"] ~doc)

let atoms =
  let doc = "Include the 'order' statement with the list of all atoms in the input formula (experimental feature)." in
  Arg.(value & flag & info ["al"] ~doc)

let inFilename =
  let doc = "Specify the input file. If not given, stdin is used." in
  Arg.(value & opt (some file) None & info ["i"] ~doc)

let outFilename =
  let doc = "Specify the output file. If not given, stdout is used." in
  Arg.(value & opt (some string) None & info ["o"] ~doc)

let main_t = Term.(const main $ verbose $ useSimplification $ useFOrenaming $ atoms $ inFilename $ outFilename)

let cmd =
  let info = Cmd.info "translate" in
  Cmd.v info main_t

let () = exit (Cmd.eval cmd)
