(*
 * parser.ml --- TLA+ parser
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** TLA+ parsing setup. The actual parsers are distributed in the
    following individual modules: {ul
    {- {!Expr.Parser}}
    {- {!Proof.Parser}}
    {- {!Module.Parser}}} *)

open Ext

(** TLA+ tokens *)
module Token = struct

  type token_ =
    | BOF                               (* beginning of file *)
    | ID of string                      (* identifiers *)
    | OP of string                      (* operators *)
    | KWD of string                     (* keywords *)
    | NUM of string * string            (* numbers *)
    | STR of string                     (* strings *)
    | PUNCT of string                   (* misc. punctuation *)
    | ST of [`Star | `Plus | `Num of int] * string * int
                                        (* step token *)

  and token = { form : token_ ;
                mutable rep : string ;
                loc  : Loc.locus }

  let locus t = t.loc

  let bof loc = { form = BOF ; rep = "start of file" ; loc = loc }

  let rep t = match t.rep with
    | "" ->
        let trep = begin match t.form with
          | BOF -> "start of file"
          | ID x -> "identifier " ^ x
          | KWD x -> "keyword " ^ x
          | OP x -> "operator " ^ x
          | PUNCT x -> x
          | NUM (m, "") -> m
          | NUM (m, n) -> m ^ "." ^ n
          | STR s -> "\"" ^ s ^ "\""
          | ST (`Star, sl, ds) -> "<*>" ^ sl ^ String.make ds '.'
          | ST (`Plus, sl, ds) -> "<+>" ^ sl ^ String.make ds '.'
          | ST (`Num m, sl, ds) -> "<" ^ string_of_int m ^ ">" ^ sl ^ String.make ds '.'
        end in
        t.rep <- trep ;
        trep
    | rep -> rep

  let eq s t = s.form = t.form

  let pp_print_token ff t =
    Format.pp_print_string ff (rep t)

end

(** TLA+ precedence *)
module Prec = struct

  (** A precedence is a range of values. Invariant: the first
      component must be less than or equal to the second component. *)
  type prec = int * int

  (** Check that the first precedence range is completely below the
      second range. *)
  let below (a, b) (c, d) = b < c

  (** Check if the two given precedence ranges overlap. *)
  let conflict (a, b) (c, d) =
    (a <= c && c <= b) || (c <= a && a <= d)
end

module Fu = Fmtutil.Minimal (Prec)

module P = Pars.Pco.Make (Token) (Prec)

open P

(** The [pcx] is the state carried by the parsers. The [ledge] field
    contains the left edge of the active rectangle of input. *)
type pcx = {
  ledge : int ;
  clean : bool ;
}

let init = { ledge = -1 ; clean = true }

type 'a prs = (pcx, 'a) P.prs
type 'a lprs = 'a prs Lazy.t

let locate p =
  withloc p <$> begin
    fun (a, loc) -> Util.set_locus (Property.noprops a) loc
  end

let scan ts =
  get >>= fun px ->
    P.scan begin
      fun t ->
        if px.ledge <= Loc.column t.Token.loc.Loc.start then ts t.Token.form
        else None
    end

open Token

let punct p = scan begin
  function
    | PUNCT q when q = p -> Some p
    | _ -> None
end

let kwd k = scan begin
  fun tok ->
    match tok with
      | KWD j when j = k -> Some k
      | _ -> None
end

module Op = Optable

let anyinfix = scan begin
  function
    | OP p ->
        let rec loop = function
          | [] -> None
          | ({ Op.fix = Op.Infix _ } as top) :: _ -> Some (top.Op.name)
          | _ :: tops -> loop tops
        in loop (Hashtbl.find_all Op.optable p)
    | _ -> None
end

let infix o = anyinfix <?> (fun p -> o = p)

let anyprefix = scan begin
  function
    | OP p ->
        let rec loop = function
          | [] -> None
          | ({ Op.fix = Op.Prefix } as top) :: _ -> Some (top.Op.name)
          | _ :: tops -> loop tops
        in loop (Hashtbl.find_all Op.optable p)
    | _ -> None
end

let prefix o = anyprefix <?> (fun p -> o = p)

let anypostfix = scan begin
  function
    | OP p ->
        let rec loop = function
          | [] -> None
          | ({ Op.fix = Op.Postfix } as top) :: _ -> Some (top.Op.name)
          | _ :: tops -> loop tops
        in loop (Hashtbl.find_all Op.optable p)
    | _ -> None
end

let anyop = scan begin
  function
    | OP o ->
        let op = Hashtbl.find Optable.optable o in
          Some op.Optable.name
    | _ -> None
end

let anyident = scan begin
  function
    | ID i -> Some i
    | _ -> None
end

let ident i = anyident <?> (fun j -> i = j)

let anyname = scan begin
  function
    | ID nm | KWD nm -> Some nm
    | _ -> None
end

let number = scan begin
  function
    | NUM (m, n) -> Some (m, n)
    | _ -> None
end

let nat = scan begin
  function
    | NUM (m, "") -> Some (int_of_string m)
    | _ -> None
end

let str = scan begin
  function
    | STR (s) -> Some (s)
    | _ -> None
end

let pragma p = punct "(*{" >>> p <<< punct "}*)"

(*****************************************************************)

(* Function: [pickle : string -> string]

   Transcode a TLA+ identifier into an identifier suitable for all the
   back-end provers.

   The result must match [a-zA-Z]([a-zA-Z0-9_]*[a-zA-Z])?
   There are a number of keywords that must be avoided:
   Isabelle keywords, Isabelle/TLA+ identifiers, some keywords of the SMT
   provers.
   The [pickle] function must be injective, and its range must not include
   any identifier starting with "str_", "prm_", or any three letters
   followed by an underscore.

   Algorithm:
   - if the identifier has no special characters, starts and ends with a
     letter, and is not one of the keywords, leave it alone.
   - otherwise:
     + first replace every character not in [a-zA-Z0-9] with a 4-letter
       name followed by an underscore
     + then prepend "a_" and append "a"
*)

let charname c =
  match c with
  | '!'  -> Some "excl_"
  | '#'  -> Some "hash_"
  | '$'  -> Some "doll_"
  | '%'  -> Some "perc_"
  | '&'  -> Some "ampe_"
  | '\'' -> Some "quot_"
  | '('  -> Some "lpar_"
  | ')'  -> Some "rpar_"
  | '*'  -> Some "star_"
  | '+'  -> Some "plus_"
  | '-'  -> Some "dash_"
  | '.'  -> Some "peri_"
  | '/'  -> Some "slas_"
  | ':'  -> Some "colo_"
  | '<'  -> Some "less_"
  | '='  -> Some "equa_"
  | '>'  -> Some "more_"
  | '?'  -> Some "ques_"
  | '@'  -> Some "atsi_"
  | '['  -> Some "lbrk_"
  | '\\' -> Some "bksl_"
  | ']'  -> Some "rbrk_"
  | '^'  -> Some "care_"
  | '_'  -> Some "unde_"
  | '|'  -> Some "vert_"
  | '~'  -> Some "tild_"
  | 'a'..'z' | 'A'..'Z' | '0'..'9' -> None
  | _ -> assert false
;;

let has_special_chars s =
  try
    for i = 0 to String.length s - 1 do
      if charname s.[i] <> None then raise Exit;
    done;
    false
  with Exit -> true
;;

let isabelle_tlaplus_keys = [
    (* Isabelle/TLA+ types and definitions -- see tools/all_defs.sml *)
    "All"; "Append"; (* "BOOLEAN"; *) "Bijections"; "Case";
    "CaseArm"; "CaseOther"; "Char"; "Choice"; (* "DOMAIN"; *)
    "EnumFuncSet"; "Ex"; (* "FALSE"; *) "Fcn"; "FuncSet"; "INTER";
    "Id"; "Image"; "Injections"; "Injective"; "InjectiveOn"; "Int";
    "Inverse"; "Len"; "Let"; "Monotonic"; "Nat"; "Nibble"; "Not";
    "PeanoAxioms"; "Pred"; "Product"; "Range"; (* "SUBSET"; *)
    "Seq"; "String"; "Succ"; "Surjections"; "Surjective";
    (* "TRUE"; *) "TYPE"; "Trueprop"; (* "UNION"; *) "Zero"; "abs";
    "addElt"; "addnat"; "all"; "antisymmetric"; "any"; "aprop";
    "arbitrary"; "args"; "arith_add"; "asms"; "bAll"; "bChoice";
    "bEx"; "boolify"; "c"; "cap"; "cargs"; "case_arm"; "case_arms";
    "cases_conj"; "cases_equal"; "cases_forall"; "cases_implies";
    "char"; "cidts"; "classes"; "cond"; "conj"; "conjunction";
    "converse"; "cs"; "cup"; "default"; "diff"; "diffnat"; "disj";
    "div"; "divmodNat"; "divmod_rel"; "domrng"; "domrngs"; "dummy";
    "dummy_pattern"; "dvd"; "emptySeq"; "eq"; "equivalence";
    "except"; "extend"; "fapply"; "float_const"; "float_token";
    "fun"; "geq"; "gfp"; "greater"; "id"; "idt"; "idts"; "iff";
    "imp"; "in"; "index"; "infinity"; "irreflexive"; "isAFcn";
    "isASeq"; "isBool"; "isNeg"; "isPos"; "itself"; "leq"; "less";
    "letbind"; "letbinds"; "lfp"; "logic"; "longid"; "minus";
    "mod"; "mult"; "multnat"; "natInterval"; "num"; "num_const";
    "oneArg"; "prod"; "prop"; "psubset"; "psupset"; "pttrn";
    "pttrns"; "reflexive"; "rel_comp"; "rel_domain"; "rel_image";
    "rel_range"; "setOfAll"; "setOfPairs"; "setminus"; "sgn";
    "sort"; "sort_constraint"; "struct"; "subsetOf"; "subseteq";
    "symmetric"; "term"; "tid"; "tpl"; "transitive"; "tvar";
    "type"; "types"; "upair"; "upto"; "var"; "xcpt"; "xnum";
    "xstr";
  ]
;;

(* FIXME this list is obviously incomplete *)
let other_keys = [
  "O";      (* "apparently illegal" [Kaustuv, commit 16156] *)
  "max";    (* reserved word in Z3 v4.0 *)
  "status"; (* keyword in Spass *)
];;

module SS = Set.Make (String);;

let forbidden =
  let f set str = SS.add str set in
  let res = List.fold_left f SS.empty isabelle_tlaplus_keys in
  let res = List.fold_left f res Isabelle_keywords.v in
  let res = List.fold_left f res other_keys in
  res
;;

let is_nonletter c =
  match c with
  | 'a'..'z' | 'A'..'Z' -> false
  | _ -> true
;;

let pickle id =
  (* uncomment this to detect double-pickling
     It cannot go into production code because it also breaks when some user
     identifier begins with "a_".
     assert (String.length id < 2 || id.[0] <> 'a' || id.[1] <> '_');
  *)
  if is_nonletter id.[0]
     || is_nonletter id.[String.length id - 1]
     || has_special_chars id
     || SS.mem id forbidden
  then begin
    let b = Buffer.create 20 in
    for i = 0 to String.length id - 1 do
      match charname id.[i] with
      | Some s -> Buffer.add_string b s
      | None -> Buffer.add_char b id.[i]
    done;
    "a_" ^ Buffer.contents b ^ "a"
  end else begin
    id
  end
;;
