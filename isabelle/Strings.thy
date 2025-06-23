(*  Title:      TLA+/Strings.thy
    Author:     Stephan Merz, Inria Nancy
    Copyright (C) 2009-2025  INRIA and Microsoft Corporation
    License:    BSD
    Version:    Isabelle2025
*)

section \<open> Characters and strings \<close>

theory Strings
imports Tuples
begin

subsection \<open> Characters \<close>

text \<open>
  Characters are represented as pairs of hexadecimal digits (also called
  \emph{nibbles}).
\<close>

definition Nibble
(*  where "Nibble \<equiv> {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15}" *)
  where "Nibble \<equiv> {0, 
                    1, 
                    succ[1], 
                    succ[succ[1]], 
                    succ[succ[succ[1]]],
                    succ[succ[succ[succ[1]]]],
                    succ[succ[succ[succ[succ[1]]]]],
                    succ[succ[succ[succ[succ[succ[1]]]]]],
                    succ[succ[succ[succ[succ[succ[succ[1]]]]]]],
                    succ[succ[succ[succ[succ[succ[succ[succ[1]]]]]]]],
                    succ[succ[succ[succ[succ[succ[succ[succ[succ[1]]]]]]]]],
                    succ[succ[succ[succ[succ[succ[succ[succ[succ[succ[1]]]]]]]]]],
                    succ[succ[succ[succ[succ[succ[succ[succ[succ[succ[succ[1]]]]]]]]]]],
                    succ[succ[succ[succ[succ[succ[succ[succ[succ[succ[succ[succ[1]]]]]]]]]]]],
                    succ[succ[succ[succ[succ[succ[succ[succ[succ[succ[succ[succ[succ[1]]]]]]]]]]]]],
                    succ[succ[succ[succ[succ[succ[succ[succ[succ[succ[succ[succ[succ[succ[1]]]]]]]]]]]]]]}"

definition char   (* -- @{text char} is intended to be applied to nibbles *)
where "char(a,b) \<equiv> \<langle>a,b\<rangle>"

lemma charInj [simp]: "(char(a,b) = char(c,d)) = (a=c \<and> b=d)"
by (simp add: char_def)

(*** example **
lemma "char(3,13) \<noteq> char(14,2)"
  by (simp add: two_def three_def four_def five_def six_def seven_def eight_def
                nine_def ten_def eleven_def twelve_def thirteen_def fourteen_def)
***)

definition Char
where "Char \<equiv> { char(a, b) : \<langle>a,b\<rangle> \<in> Nibble \<times> Nibble }"

lemma isChar [simp]: "(c \<in> Char) = (\<exists>a,b \<in> Nibble : c = char(a,b))"
unfolding Char_def by auto


subsection \<open> Strings \<close>

definition String
where "String \<equiv> Seq(Char)"

syntax
  "_Char"   :: "str_token \<Rightarrow> c"    ("CHAR _")
  "_String" :: "str_token \<Rightarrow> c"    ("_")

text \<open>
  The following parse and print translations convert between the internal
  and external representations of strings. Strings are written using
  two single quotes in Isabelle, such as \verb|''abc''|. Note that the
  empty string is just the empty sequence in \tlaplus{}, so \verb|''''| gets
  printed as @{term "\<langle>\<rangle>"}. Single characters are printed in the form
  \verb|CHAR ''a''|: Isabelle doesn't provide single characters in its
  lexicon.
\<close>

parse_ast_translation \<open>
  let
    (* convert an ML integer to a nibble *)
    fun mkNibble n =
      if n = 0
      then Ast.Constant "Integers.zero"
      else Ast.Appl [Ast.Constant "Functions.fapply", Ast.Constant "Integers.succ", mkNibble (n-1)];

    (* convert an ML character to a TLA+ Char *)
    fun mkChar c =
      if Symbol.is_ascii c
      then Ast.Appl [Ast.Constant "Strings.char",
                        mkNibble (ord c div 16), mkNibble (ord c mod 16)]
      else error ("Non-ASCII symbol: " ^ quote c);

    (* remove two leading quotes from a list of characters *)
    fun trim_quotes ("'" :: ( "'" :: cs)) = cs
      | trim_quotes cs = cs

    (* convert a list of ML characters into a TLA+ string, in reverse order *)
    fun list2TupleReverse [] = Ast.Constant "Tuples.emptySeq"
      | list2TupleReverse (c :: cs) =
          Ast.Appl [Ast.Constant "Tuples.Append", list2TupleReverse cs, mkChar c];

    (* parse AST translation for characters *)
    fun char_ast_tr [Ast.Variable str] =
      let val trimmed_str = (trim_quotes (rev (trim_quotes (Symbol.explode str))))
      in  (case trimmed_str of
            [c] => mkChar c
            | _ => error ("Expected single character, not " ^ str))
      end
    | char_ast_tr asts = raise Ast.AST ("char_ast_tr", asts);

    (* parse AST translation for strings *)
    fun string_ast_tr [Ast.Variable str] =
          list2TupleReverse (trim_quotes (rev ((trim_quotes (Symbol.explode str)))))
      | string_ast_tr asts = raise Ast.AST ("string_ast_tr", asts);
  in
    [("_Char", K char_ast_tr), ("_String", K string_ast_tr)]
  end
\<close>


(** debug **
(*declare [[syntax_ast_trace = true]]*)

lemma "''a''"
oops

lemma "''''"
oops

lemma "''abc''"
oops

lemma "CHAR ''a''"
oops

(* declare [[syntax_ast_trace = false]] *)
**)

print_ast_translation \<open>
  let
    (* convert a nibble to an ML integer *)
    (* version to be used if 2 .. 15 are definitions, not abbreviations *)
    fun destNibble (Ast.Constant @{const_syntax "zero"}) = 0
      | destNibble (Ast.Constant @{const_syntax "one"}) = 1
      | destNibble (Ast.Appl [Ast.Constant @{const_syntax "Functions.fapply"}, 
                              Ast.Constant @{const_syntax "Integers.succ"}, nb])
           = (destNibble nb) + 1
      | destNibble _ = raise Match
    (* version to be used when 2 .. 15 are abbreviations, not definitions *)
(*
    fun destNibble (Ast.Constant @{const_syntax "zero"}) = 0
      | destNibble (Ast.Constant @{const_syntax "one"}) = 1
      | destNibble (Ast.Constant @{const_syntax "two"}) = 2
      | destNibble (Ast.Constant @{const_syntax "three"}) = 3
      | destNibble (Ast.Constant @{const_syntax "four"}) = 4
      | destNibble (Ast.Constant @{const_syntax "five"}) = 5
      | destNibble (Ast.Constant @{const_syntax "six"}) = 6
      | destNibble (Ast.Constant @{const_syntax "seven"}) = 7
      | destNibble (Ast.Constant @{const_syntax "eight"}) = 8
      | destNibble (Ast.Constant @{const_syntax "nine"}) = 9
      | destNibble (Ast.Constant @{const_syntax "ten"}) = 10
      | destNibble (Ast.Constant @{const_syntax "eleven"}) = 11
      | destNibble (Ast.Constant @{const_syntax "twelve"}) = 12
      | destNibble (Ast.Constant @{const_syntax "thirteen"}) = 13
      | destNibble (Ast.Constant @{const_syntax "fourteen"}) = 14
      | destNibble (Ast.Constant @{const_syntax "fifteen"}) = 15
      | destNibble _ = raise Match;
*)
    (* convert a pair of nibbles to an ML character *)
    fun destNbls nb1 nb2 =
        let val specials = raw_explode "\"\\`'"
            val c = chr (destNibble nb1 * 16 + destNibble nb2)
        in  if not (member (op =) specials c) andalso Symbol.is_ascii c
               andalso Symbol.is_printable c
            then c else raise Match
        end;

    (* convert a TLA+ Char to an ML character *)
    fun destChar (Ast.Appl [Ast.Constant @{const_syntax "char"}, nb1, nb2]) =
          destNbls nb1 nb2
      | destChar arg = raise Match

    (* convert a TLA+ tuple (an argument of @tuple) into a list *)
    fun tuple2List (Ast.Appl[Ast.Constant "@app", tp, t]) = (tuple2List tp) @ [t]
      | tuple2List t = [t];

    (* convert a list of TLA+ characters to the output representation of a TLA+ string *)
    fun list2String cs =
          Ast.Appl [Ast.Constant "_inner_string",
                       Ast.Variable (Lexicon.implode_str cs)];

    (* print AST translation for single characters that do not occur in a string *)
    fun char_ast_tr' [nb1, nb2] =
        Ast.Appl [Ast.Constant @{syntax_const "_Char"}, list2String [destNbls nb1 nb2]]
      | char_ast_tr' _ = raise Match

    (* print AST translation for non-empty literal strings,
       fails (by raising exception Match)
       when applied to anything but a character sequence *)
    fun string_ast_tr' [args] = list2String (map destChar (tuple2List args))
      | string_ast_tr' _ = raise Match;
  in
    [(@{const_syntax "char"}, K char_ast_tr'), ("@tuple", K string_ast_tr')]
  end
\<close>

(*** examples **
(*declare [[syntax_ast_trace = true]]*)

lemma "CHAR ''a'' \<noteq> CHAR ''b''"
by simp

lemma "''abc'' \<noteq> ''abd''"
by simp

lemma "''ao'' \<noteq> ''''"
by simp

lemma "'''' \<noteq> ''a''"
by simp

lemma "''ab''[1] = CHAR ''a''"
by simp

lemma "''abc''[2] \<noteq> CHAR ''a''"
by (simp add: two_def)

(* declare [[syntax_ast_trace = false]] *)

**)


subsection \<open> Records and sets of records \<close>

text \<open>
  Records are simply represented as enumerated functions with string arguments,
  such as @{text "(''foo'' :> 1) @ (''bar'' :> TRUE)"}. Similarly, there is no
  specific @{text "EXCEPT"} construct for records; use the standard one for
  functions, such as @{text "[r EXCEPT ![''foo'' = 3]]"}. Finally, sets of
  records are represented as sets of enumerated functions as in
  @{text "[''foo'' : Nat, ''bar'' : BOOLEAN]"}. Support for standard \tlaplus{}
  record syntax in Isabelle seems difficult, because the Isabelle lexer
  distinguishes between identifiers and strings: the latter must be surrounded
  by two single quotes.
\<close>

(** Examples **

lemma "(''foo'' :> 1 @@ ''bar'' :> TRUE) \<in> [''bar'' : BOOLEAN, ''foo'' : Nat]"
by auto   (* slow *)

lemma "r \<in> [''bar'' : BOOLEAN, ''foo'' : Nat]
       \<Longrightarrow> [r EXCEPT ![''foo''] = 3] \<in> [''bar'' : BOOLEAN, ''foo'' : Nat]"
by (force simp: two_def three_def)   (* even slower, "auto" also works *)

lemma "(''a'' :> 1) \<noteq> (''b'' :> 1)"
by simp

lemma "(''a'' :> 1 @@ ''b'' :> 2) \<noteq> (''a'' :> 1)"
by simp

lemma "(''a'' :> 1 @@ ''b'' :> 2) \<noteq> (''a'' :> 1 @@ ''b'' :> 3)"
by (simp add: two_def three_def)

lemma "(''a'' :> 1 @@ ''b'' :> 2) = (''b'' :> 2 @@ ''a'' :> 1)"
by simp

lemma "''ab'' = [i \<in> {1,2} \<mapsto> ''ab''[i]]"
by (auto simp: two_def)

lemma "''ab'' = (1 :> CHAR ''a'') @@ (2 :> CHAR ''b'')"
by (auto simp: two_def)

lemma "Len(''ab'') = 2"
by (simp add: two_def)

**)

end

(* NB: Make sure that the following is proved automatically once concatenation is defined:

THEOREM Thm1 == "ab" = "a" \o "b"
OBVIOUS

*)
