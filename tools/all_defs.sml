local

datatype bst = E | N of bst * string * bst

fun add (v, E) = N (E, v, E)
  | add (v, N (l, x, r)) =
    (case String.compare (v, x) of
       LESS => N (add (v, l), x, r)
     | EQUAL => N (l, x, r)
     | GREATER => N (l, x, add (v, r)))

fun member_of (v, E) = false
  | member_of (v, N (l, x, r)) =
    case String.compare (v, x) of
      LESS => member_of (v, l)
    | EQUAL => true
    | GREATER => member_of (v, r)

fun add_list bst l =
    List.foldl add l bst

val good_names =
    add_list
      [ "TRUE", "FALSE", "SUBSET", "UNION",
        "BOOLEAN", "DOMAIN" ]
      E

fun name_surgery nm =
  let val comps = String.tokens (fn x => x = #".") nm
      val nm = List.hd (List.rev comps)
      fun test c =
        c = #"_" orelse Char.isAlphaNum c
  in
    if List.all test (String.explode nm)
    then let in
      TextIO.output (TextIO.stdErr, "Passing: " ^ nm ^ "\n") ;
      SOME nm
    end else let in
      TextIO.output (TextIO.stdErr, "Ignoring: " ^ nm ^ "\n") ;
      NONE
    end
  end

fun output_bst oc bst =
    let fun spin cpos =
            fn E => cpos
             | N (l, x, r) =>
               let
                 val x = if member_of (x, good_names) then
                           " (* \"" ^ x ^ "\"; *)"
                         else " \"" ^ x ^ "\";"
                 val cpos = spin cpos l
                 val cpos =
                     if cpos + String.size x >= 70
                     then (TextIO.output (oc, "\n     "); 5)
                     else cpos
                 val _ = TextIO.output (oc, x)
                 val cpos = cpos + String.size x
               in
                 spin cpos r
               end
    in
      TextIO.output (oc, "     ") ;
      spin 5 bst
    end

fun specs th =
  let val fst = fn (a, b) => a
      val th = Option.valOf (ThyInfo.lookup_theory th)
      val types = #types (Type.rep_tsig (Sign.tsig_of th))
      val types = Name_Space.dest_table types
      val types = List.mapPartial (name_surgery o fst) types
      val defs = Theory.defs_of th
      val specs = Defs.all_specifications_of defs
      val specs = List.mapPartial (name_surgery o fst) specs
      val consts = Sign.consts_of th
      val consts = #constants (Consts.dest consts)
      val consts = Name_Space.dest_table consts
      val consts = List.mapPartial (name_surgery o fst) consts
      val bst = add_list types E
      val bst = add_list specs bst
      val bst = add_list consts bst
  in
    bst
  end

fun specs_saver file th =
  let val out = TextIO.openOut file in
    output_bst out (specs th) ;
    TextIO.closeOut out
  end

val _ = specs_saver "/tmp/constants.txt" "Constant"

in

val _ = TextIO.print "Constants saved in /tmp/constants.txt\n"

val _ = exit 0

end
