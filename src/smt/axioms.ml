(* SMT axioms.

Copyright (C) 2010-2013  INRIA and Microsoft Corporation
*)
open Ext
open Format
open Fmtutil
open Tla_parser
open Property

open Expr.T
open Expr.Subst
open Proof.T

module Smt = Smtcommons
module B = Builtin
module Dq = Deque
module SSet = Smt.SSet
module SMap = Smt.SMap
module T = Typ_t

let ( |>> ) = Smt.( |>> )
let ( ||> ) = Smt.( ||> )

let map = List.map

(****************************************************************************)

(** TPTP syntax only allows identifiers [a-z][a-zA-z0-9_]* *)
let m_tla = function
  | B.STRING -> "tla__STRING"
  | B.BOOLEAN -> "tla__BOOLEAN"
  | B.SUBSET -> "tla__SUBSET"
  | B.UNION -> "tla__UNION"
  | B.DOMAIN -> "tla__DOMAIN"
  | B.Subseteq -> "tla__subseteq"
  | B.Mem -> "tla__in"
  | B.Notmem -> "tla__notin"
  | B.Setminus -> "tla__setminus"
  | B.Cap -> "tla__cap"
  | B.Cup -> "tla__cup"

  | B.Int   -> "tla__Int"
  | B.Nat   -> "tla__Nat"
  | B.Real  -> "tla__Real"
  | B.Plus  -> "tla__plus"
  | B.Minus -> "tla__minus"
  | B.Times -> "tla__times"
  | B.Exp   -> "tla__exp"
  | B.Ratio -> "tla__ratio"
  | B.Quotient -> "tla__div"
  | B.Remainder -> "tla__mod"
  | B.Lt    -> "tla__lt"
  | B.Lteq  -> "tla__le"
  | B.Gt    -> "tla__lt" (* abbrev *)
  | B.Gteq  -> "tla__le" (* abbrev *)
  | B.Uminus-> "tla__uminus"
  | B.Range -> "tla__Range"
  | B.Infinity -> "tla__Infinity"

  | B.Seq -> "tla__Seq"
  | B.Len -> "tla__Len"
  | B.BSeq -> "tla__BSeq"
  | B.Cat -> "tla__concat"
  | B.Append -> "tla__Append"
  | B.Head -> "tla__Head"
  | B.Tail -> "tla__Tail"
  | B.SubSeq -> "tla__SubSeq"
  | B.SelectSeq -> "tla__SelectSeq"
  | _ -> raise Not_found

(****************************************************************************)

type smtsort = U | SBool | SInt | SStr | SField | SOp

let sort_of_type = function
  | T.Bool -> SBool
  | T.Int -> SInt
  | T.Ref (_,T.Int,_) -> SInt
  | T.Str -> SStr
  | T.Ref (_,T.Str,_) -> SStr
  (* | Rec _ -> SField *)
  | _ -> U

(* type fixity_type = Nonfix | Prefix | Infix

(* Only for TPTP-Fof. Disequalities and Arith are Prefix because are not supported by Fof. *)
let fixity = function
  | B.Conj | B.Disj | B.Implies | B.Equiv | B.Eq ->
      Infix
  | B.Neg | B.Uminus
  | B.Plus | B.Minus | B.Times | B.Ratio | B.Quotient | B.Remainder | B.Exp
  | B.Lt | B.Lteq | B.Gt | B.Gteq ->
      Prefix
  | B.TRUE | B.FALSE
  | _ -> Nonfix *)

type t_map = {
    op : Builtin.builtin -> string ;
    print_sort : smtsort -> string ;
    apply : 'a. ?isinfix:bool -> Format.formatter -> string -> (Format.formatter -> 'a -> unit) -> 'a list -> unit ;
    quant : 'a. Format.formatter -> Expr.T.quantifier -> 'a option -> (string * smtsort) list -> (Format.formatter -> 'a -> unit) -> 'a -> unit ;
    ite : string option ;
    uminus : 'a. Format.formatter -> (Format.formatter -> 'a -> unit) -> 'a -> unit ;
}

let smtlib_map : t_map = {
  op = begin function
    | B.TRUE    -> "true"
    | B.FALSE   -> "false"
    | B.Conj    -> "and"
    | B.Disj    -> "or"
    | B.Implies -> "=>"
    | B.Equiv   -> "="
    | B.Eq      -> "="
    | B.Neg     -> "not"
    | B.Plus    -> "+"
    | B.Minus   -> "-"
    | B.Times   -> "*"
    | B.Ratio   -> "/"
    | B.Quotient -> "div"
    | B.Remainder -> "mod"
    | B.Exp     -> "exp"    (** "exp" is natively declared only in Z3 *)
    | B.Lt      -> "<"
    | B.Lteq    -> "<="
    (* | B.Gt      -> ">" *)
    (* | B.Gteq    -> ">=" *)
    | B.Uminus  -> "-"
    | _ -> assert false
    end ;
  print_sort = begin function
    | U      -> "u"
    | SBool  -> "Bool"
    | SInt   -> "Int"
    | SStr   -> "str"
    | SField -> "tla_Field"
    | SOp    -> "tla_Op"
    end ;
  apply = begin fun ?isinfix ff id ppargs args ->
    fprintf ff "@[<hov2>(%s@ @[<hov0>%a@])@]" id
      (pp_print_delimited ~sep:pp_print_space ppargs) args
    end ;
  ite = Some "ite" ;
  (** CVC4: "A quantified variable may not be of type BOOLEAN" *)
  quant = begin fun ff q pat vs ppex ex ->
    let q = match q with Forall -> "forall" | Exists -> "exists" in
    fprintf ff "@[<hov2>(%s@ (@[<v>%s@])@ %s%a%s%a%s)@]" q
      (vs |> List.map (fun (v,t) -> sprintf "@[(%s %s)@]" v
              (match t with SBool -> "Bool" | SInt -> "Int" | SStr -> "str" | SField -> "tla_Field" | _ -> "u"))
          |> String.concat " ")
      (if Option.is_some pat then "(! " else "")
      ppex ex
      (if Option.is_some pat then " :pattern (" else "")
      (if Option.is_some pat then ppex else (fun _ _ -> ()))
      (if Option.is_some pat then Option.get pat else ex)
      (if Option.is_some pat then "))" else "")
    end ;
  uminus = fun ff -> fprintf ff "(- %a)";
}

let yices_map : t_map = {
  op = begin function
    | B.TRUE    -> "true"
    | B.FALSE   -> "false"
    | B.Conj    -> "and"
    | B.Disj    -> "or"
    | B.Implies -> "=>"
    | B.Equiv   -> "="
    | B.Eq      -> "="
    | B.Neg     -> "not"
    | B.Plus    -> "+"
    | B.Minus   -> "-"
    | B.Times   -> "*"
    | B.Ratio   -> "/"
    | B.Quotient -> "div"
    | B.Remainder -> "mod"
    | B.Exp     -> "^"
    | B.Lt      -> "<"
    | B.Lteq    -> "<="
    (* | B.Gt      -> ">" *)
    (* | B.Gteq    -> ">=" *)
    | B.Uminus  -> "-"
    | _ -> assert false
    end ;
  print_sort = begin function
    | U      -> "u"
    | SBool  -> "bool"
    | SInt   -> "int"
    | SStr   -> "str"
    | SField -> "tla_Field"
    | SOp    -> "tla_Op"
    end ;
  apply = (fun ?isinfix ff id ppargs args ->
    fprintf ff "@[<hov2>(%s@ @[<hov0>%a@])@]" id
      (pp_print_delimited ~sep:pp_print_space ppargs) args) ;
  ite = Some "ite" ;
  quant = begin fun ff q pat vs ppex ex ->
    let q = match q with Forall -> "forall" | Exists -> "exists" in
    fprintf ff "@[<hov2>(%s@ (@[<v>%s@])@ %a)@]" q
      (vs |> List.map (fun (v,t) -> sprintf "@[%s::%s@]" v
              (match t with SBool -> "bool" | SInt -> "int" | SStr -> "str" | SField -> "tla_Field" | _ -> "u"))
          |> String.concat " ")
      ppex ex
    end ;
  uminus = fun ff -> fprintf ff "-%a" ;
}

let dfg_map : t_map = {
  op = begin function
    | B.TRUE    -> "true"
    | B.FALSE   -> "false"
    | B.Conj    -> "and"
    | B.Disj    -> "or"
    | B.Implies -> "implies"
    | B.Equiv   -> "equiv"
    | B.Eq      -> "equal"
    | B.Neg     -> "not"
    | B.Plus    -> "plus"
    | B.Minus   -> "minus"
    | B.Times   -> "mult"
    | B.Ratio   -> "fract"
    | B.Quotient -> "div"
    | B.Remainder -> "mod"
    | B.Exp     -> "exp"
    | B.Lt      -> "ls"
    | B.Lteq    -> "le"
    (* | B.Gt      -> "gs" *)
    (* | B.Gteq    -> "ge" *)
    | B.Uminus  -> "-"
    | _ -> assert false
    end ;
  print_sort = begin function
    | SInt   -> ":Integer"
    | _ -> ""
    end ;
  apply = (fun ?isinfix ff id ppargs args ->
    fprintf ff "@[<hov2>%s(@[<hov0>%a@])@]" id
      (pp_print_delimited ~sep:pp_print_commasp ppargs) args) ;
  ite = None ;
  quant = begin fun ff q pat vs ppex ex ->
    let q = match q with Forall -> "forall" | Exists -> "exists" in
    fprintf ff "@[<hov2>%s([[@<v>%s@]],@ %a)@]" q
      (vs |> List.map (fun (v,s) -> sprintf "%s%s" v (match s with SBool -> ":Bool" | SInt -> ":Integer" | _ -> ""))
          |> String.concat ",")
      ppex ex
    end ;
  uminus = fun ff -> fprintf ff "-%a" ;
}

let fof_map : t_map = {
  op = begin function
    | B.TRUE    -> "$true"
    | B.FALSE   -> "$false"
    | B.Conj    -> " & "
    | B.Disj    -> " | "
    | B.Implies -> " => "
    | B.Equiv   -> " <=> "
    | B.Eq      -> " = "
    | B.Neg     -> "~"
    | B.Plus    -> "tptp_plus"
    | B.Minus   -> "tptp_minus"
    | B.Times   -> "tptp_times"
    | B.Ratio   -> "tptp_ratio"
    | B.Quotient -> "tptp_div"
    | B.Remainder -> "tptp_mod"
    | B.Exp     -> "tptp_exp"
    | B.Lt      -> "tptp_ls"
    | B.Lteq    -> "tptp_le"
    (* | B.Gt      -> "tptp_gs" *)
    (* | B.Gteq    -> "tptp_ge" *)
    | B.Uminus  -> "tptp_uminus"
    | e ->
        (* Util.eprintf "Expr: %a" (print_prop ()) (noprops (Internal e)) ; *)
        Printf.eprintf "FOF unsupported builtin expression\n" ; assert false
    end ;
  print_sort = begin function
    | _ -> ""
    end ;
  apply = begin fun ?isinfix ff id ppargs args ->
    let pp_print_sep op ff () =
      pp_print_cut ff () ;
      pp_print_string ff id
    in
    match id, args with
    | "int2u", [x] | "str2u", [x] ->
        fprintf ff "@[%a@]" ppargs x                                          (** Do not print those [id]s. *)
    | _ when isinfix = Some true ->
      (* fixity op = Infix ->  *)
        fprintf ff "@[<hov0>(@[<hov0>%a@])@]"
          (pp_print_delimited ~sep:(pp_print_sep id) ppargs) args
    | _ ->
        fprintf ff "@[<hov2>%s(@[<hov0>%a@])@]" id
          (pp_print_delimited ~sep:pp_print_commasp ppargs) args
    end ;
  ite = None ;
  quant = begin fun ff q pat vs ppex ex ->
    let q = match q with Forall -> "!" | Exists -> "?" in
    fprintf ff "@[<hov2>(%s [@[<v>%s@]]:@ %a)@]" q
      (String.concat "," (List.map (fun (v,_) -> sprintf "%s" v) vs))
      ppex ex
    end ;
  uminus = fun ff -> fprintf ff "uminus(%a)" ;
}

let m_apply m ii id (args:string list) : string =
  ignore (Format.flush_str_formatter ());
  m.apply ~isinfix:ii Format.str_formatter id pp_print_string args;
  Format.flush_str_formatter ()

let m_quant m q vs (ex:string) : string =
  ignore (Format.flush_str_formatter ());
  m.quant Format.str_formatter q None vs pp_print_string ex;
  Format.flush_str_formatter ()

let m_uminus m (ex:string) : string =
  ignore (Format.flush_str_formatter ());
  m.uminus Format.str_formatter pp_print_string ex;
  Format.flush_str_formatter ()

(****************************************************************************)

(* let smap : t_map = set_map () *)

(** Returns (id,arg types,ret type,axioms,dependencies) *)
let build_tla_ops (smap:t_map) std_set (* tuples record_ids *) =
  (* let op o = smap.op o in *)
  let app op es = m_apply smap false op es in
  let infix b es = m_apply smap true (smap.op b) es in
  let neg x = app (smap.op B.Neg) [x] in
  let app1 op x     = app op [x] in
  let app2 op x y   = app op [x ; y] in
  let app2_op o x y = app2 (smap.op o) x y in
  let mem x y     = app (m_tla B.Mem) [x ; y] in
  let implies x y = infix B.Implies [x ; y] in
  let eq x y      = infix B.Eq [x ; y] in
  let equiv x y   = infix B.Equiv [x ; y] in
  let lt x y      = if !Smt.mode = Smt.Spass || !Smt.mode = Smt.Fof then app2_op B.Lt x y else infix B.Lt [x ; y] in
  let leq x y     = if !Smt.mode = Smt.Spass || !Smt.mode = Smt.Fof then app2_op B.Lteq x y else infix B.Lteq [x ; y] in
  let lAnd xs     = match xs with [x] -> x | _ -> infix B.Conj xs in
  let lOr xs      = match xs with [x] -> x | _ -> infix B.Disj xs in
  (* let isint x     = app "isint" [x] in    (** Only for Fof and Spass with Integers! *) *)
  let boolify x   = app "boolify" [x] in
  let bool2u x    = app "bool2u" [x] in
  let int2u x     = app "int2u" [x] in    (** Fof and Spass will print [x] and ignore the lifting *)
  let str2u x     = app "str2u" [x] in    (** Fof and Spass will print [x] and ignore the lifting *)
  let fcnapp1 f x = app2 Smt.fcnapp f x in
  let dom e       = app (m_tla B.DOMAIN) [e] in
  let forall      = m_quant smap Forall in
  let exists      = m_quant smap Exists in
  let pattern e ps =
    match !Smt.mode with
    | Smt.Spass | Smt.Fof | Smt.Yices -> e
    | _ -> sprintf "@[<hov2>(! %s :pattern (%s))@]" e (String.concat " " ps)
  in
  let pattern_z3 e ps =       (** same as pattern, but ignored by [Smtlib]. Basically used for multi-patterns only supported by Z3. *)
    match !Smt.mode with
    | Smt.Z3 -> sprintf "@[<hov2>(! %s :pattern (%s))@]" e (String.concat " " ps)
    | _ -> e
  in
  let m = "M_"^Smt.fresh_id () in
  let n = "N_"^Smt.fresh_id () in
  let x = "X_"^Smt.fresh_id () in
  let y = "Y_"^Smt.fresh_id () in
  let z = "Z_"^Smt.fresh_id () in
  let s = "S_"^Smt.fresh_id () in
  let t = "T_"^Smt.fresh_id () in
  let i = "I_"^Smt.fresh_id () in
  let f = "F_"^Smt.fresh_id () in (* ignore(f); *)
  let g = "G_"^Smt.fresh_id () in (* ignore(g); *)

  (* let cond_arith_op      sop top =
    forall [x,U ; y,U] (implies (lAnd [isint x ; isint y])
      (eq    (app2 sop x y) (app2_op top x y))) in
  let cond_arith_op_bool sop top =
    forall [x,U ; y,U] (implies (lAnd [isint x ; isint y])
      (equiv (app2 sop x y) (app2_op top x y))) in *)
  (** FOF terms are lowercase *)
  let tla_ops_fof = [
      (* m_tla B.Int,   [], U,    [ forall [x,U] (implies (mem x (m_tla B.Int)) (isint x)) ], [m_tla B.Mem;"isint"] ; *)
      (* m_tla B.Nat,   [], U,    [ forall [x,U] (implies (mem x (m_tla B.Nat)) (lAnd [isint x ; leq "0" x])) ], [m_tla B.Mem;"isint"] ; *)
      (* m_tla B.Plus,  [U;U], U, [ cond_arith_op "tla_plus"  B.Plus ], [] ;
      m_tla B.Minus, [U;U], U, [ cond_arith_op "tla_minus" B.Minus ], [] ;
      m_tla B.Times, [U;U], U, [ cond_arith_op "tla_times" B.Times ], [] ;
      m_tla B.Exp,   [U;U], U, [ cond_arith_op "tla_exp"   B.Exp ], [] ;
      m_tla B.Quotient, [U;U], U, [ cond_arith_op "tla_div"   B.Quotient ], [smap.op B.Quotient] ;
      m_tla B.Remainder,[U;U], U, [ cond_arith_op "tla_mod"   B.Remainder ], [smap.op B.Remainder] ;
      m_tla B.Lt,    [U;U], SBool, [ cond_arith_op_bool "tla_lt"  B.Lt ], [] ;
      m_tla B.Lteq,  [U;U], SBool, [ cond_arith_op_bool "tla_leq" B.Lteq ], [] ;
      m_tla B.Range, [U;U], U, [ forall [m,U ; n,U ; x,U]
            (equiv (mem x (app2 "tla__Range" m n))
            (implies (lAnd [isint m ; isint n]) (lAnd [isint x ; leq m x ; leq x n]))) ;
        ], [m_tla B.Mem;"isint";"tla__Range"] ;
      m_tla B.Uminus, [U], U,   [ forall [n,U] (implies (isint n) (eq (app1 (m_tla B.Uminus) n) (m_uminus smap n))) ], [] ; *)
      "div",       [SInt;SInt], SInt,  [ forall [x,SInt ; y,SInt ; z,SInt]
            (implies (lt "0" y)
            (equiv (eq (app "div" [x ; y]) z)
                          (lAnd [ leq (app2_op B.Times y z) x ;
                                      leq x (app2_op B.Times y (app2_op B.Plus z "1"))]))) ], [] ;
      "mod",       [SInt;SInt], SInt,  [ forall [x,SInt ; y,SInt]
            (implies (lt "0" y)
            (eq (app "mod" [x ; y])
            (app2_op B.Minus x (app2_op B.Times (app "div" [x ; y]) y)) )) ], ["div"] ;
  ] in

  let tla_ops_spass = [
      (* "isint",     [U], SBool,[ forall [n,SInt] (isint n) ], [] ; *)
      "int2u",     [SInt], U, [ forall [x,SInt ; y,SInt] (implies (eq (int2u x) (int2u y)) (eq x y)) ], [] ;
      "str2u",     [SStr], U, [ forall [x,SStr ; y,SStr] (implies (eq (str2u x) (str2u y)) (eq x y)) ], [] ;
  ] @ tla_ops_fof
  in

  let lift_arith sop top =
    forall [m,SInt ; n,SInt] (pattern
      (eq (app2 sop (int2u m) (int2u n))
          (int2u (app2_op top m n)))
      [app2 sop (int2u m) (int2u n)])
  in
  let lift_arith_positive sop top =
    forall [m,SInt ; n,SInt] (pattern
      (implies (lt "0" n)
        (eq (app2 sop (int2u m) (int2u n))
            (int2u (app2_op top m n))))
      [app2 sop (int2u m) (int2u n)])
  in
  let lift_arith_exp sop top =                                                (** exponentiation requires its first argument to be non-zero *)
    forall [m,SInt ; n,SInt] (pattern
      (implies (neg (eq "0" m))
        (eq (app2 sop (int2u m) (int2u n))
            (int2u (app2_op top m n))))
      [app2 sop (int2u m) (int2u n)])
  in
  let lift_arith_predicate sop top =
    forall [m,SInt ; n,SInt] (pattern
      (equiv (app2 sop (int2u m) (int2u n))
             (app2_op top m n))
      [app2 sop (int2u m) (int2u n)])
  in
  let tla_ops_smtlib = [
      (* "isint",     [U], SBool,[ forall [n,SInt] (isint (int2u n)) ] @
                              [ forall [x,U] (pattern (implies (isint x) (exists [n,SInt] (eq x (int2u n)))) [isint x]) ],
                              (* [ forall [x,U] (implies (isint x) (exists [n,SInt] (eq x (int2u n)))) ],  (** CHECK: the pattern seems to choke the solver *) *)
                                  [m_tla B.Mem;"int2u"] ; *)
      (** Injective functions. *)
      (* "int2u",     [SInt], U, [ forall [x,SInt ; y,SInt] (implies (eq (int2u x) (int2u y)) (eq x y)) ], [] ; *)
      (* "str2u",     [SStr], U, [ forall [x,SStr ; y,SStr] (implies (eq (str2u x) (str2u y)) (eq x y)) ], [] ; *)
      (** From the Z3 tutorial: The quantified formula [i.e. the injectivity
          axiom with a two-part pattern] is instantiated for every pair of
          occurrences of f. A simple trick allows formulating injectivity of
          f in such a way that only a linear number of instantiations is
          required. The trick is to realize that f is injective if and only
          if it has a partial inverse. *)
      "int2u",     [SInt], U, [ forall [x,SInt] (pattern (eq (app "u2int" [int2u x]) x) [ int2u x ]) ], [ "u2int"] ;
      "u2int",     [U], SInt, [], [] ;
      "str2u",     [SStr], U, [ forall [x,SStr] (pattern (eq (app "u2str" [str2u x]) x) [ str2u x ]) ], [ "u2str"] ;
      "u2str",     [U], SStr, [], [] ;
  ] @
  if !Smt.mode <> Smt.Z3 && !Smt.mode <> Smt.CVC3 then begin [                        (** The following operators are built-in on Z3 *)
      "exp", [SInt;SInt], SInt, [], [];
      (* "div", [SInt;SInt], SInt, [ forall [x,SInt ; y,SInt ; z,SInt]
        (implies
          (lt "0" y)
          (equiv
            (eq
              (app "div" [x ; y]) z)
              (lAnd [ leq (app2_op B.Times y z) x ;
                      app (smap.op B.Lt) [x ; app2_op B.Times y (app2_op B.Plus z "1")]]))) ], [] ;
      "mod", [SInt;SInt], SInt, [ forall [x,SInt ; y,SInt]
        (implies
          (lt "0" y)
          (eq
            (app "mod" [x ; y])
            (app2_op B.Minus x (app2_op B.Times (app "div" [x ; y]) y)) )) ], ["div"] ; *)
        ] end else []
  in

  let all_std_ops =
    (match !Smt.mode with
      | Smt.Spass -> tla_ops_spass
      | Smt.Fof -> tla_ops_fof
      | _ -> tla_ops_smtlib)
    @ [
    (***  Operator name  X  argument sort list  X  return sort  X  associated axioms  X  dependent ops  *)

    (*
    (* becareful! this encoding is weaker than the one below. *)
    m_tla B.Int,   [], U, [
      forall [n,SInt] (pattern
        (mem (int2u n) (m_tla B.Int))
        [ mem (int2u n) (m_tla B.Int) ])
      ], [ m_tla B.Mem; "int2u" ] ;
    m_tla B.Nat,   [], U, [
      forall [n,SInt] (pattern
        (implies (leq "0" n) (mem (int2u n) (m_tla B.Nat)))
        [ mem (int2u n) (m_tla B.Nat) ])
      ], [ m_tla B.Mem; "int2u" ] ; *)

    "bool2u", [SBool], U, [ forall [x,SBool ; y,SBool] (implies (eq (bool2u x) (bool2u y)) (eq x y)) ], [] ;
    m_tla B.Int,   [], U, [
      forall [x,U] (pattern (equiv
        (mem x (m_tla B.Int))
        (exists [n,SInt] (eq x (int2u n))))
        [ mem x (m_tla B.Int) ])
      ], [ m_tla B.Mem; "int2u" ] ;
    m_tla B.Nat,   [], U, [
      forall [x,U] (pattern (equiv
        (mem x (m_tla B.Nat))
        (exists [n,SInt] (lAnd [eq x (int2u n) ; leq "0" n])))
        [ mem x (m_tla B.Nat) ])
      ], [ m_tla B.Mem; m_tla B.Lteq; "int2u" ] ;

    m_tla B.Plus,  [U;U], U, [ lift_arith (m_tla B.Plus)  B.Plus ], ["int2u"] ;
    m_tla B.Minus, [U;U], U, [ lift_arith (m_tla B.Minus) B.Minus ], ["int2u"] ;
    m_tla B.Times, [U;U], U, [ lift_arith (m_tla B.Times) B.Times ], ["int2u"] ;
    (* m_tla B.Exp,   [U;U], U,     [ lift_arith (m_tla B.Exp)   B.Exp ], ["int2u"] ; *)
    (* m_tla B.Exp,   [U;U], U,     [ ], [ ] ; *)
    m_tla B.Exp,   [U;U], U,     [ lift_arith_exp (m_tla B.Exp)   B.Exp ], ["int2u" ; smap.op B.Exp] ;
    m_tla B.Quotient, [U;U], U,  [ lift_arith_positive (m_tla B.Quotient)   B.Quotient ], ["int2u" ; smap.op B.Quotient] ;
    m_tla B.Remainder,[U;U], U,  [ lift_arith_positive (m_tla B.Remainder)  B.Remainder ], ["int2u" ; smap.op B.Remainder] ;
    m_tla B.Lt,    [U;U], SBool, [ lift_arith_predicate (m_tla B.Lt)   B.Lt ], ["int2u"] ;
    m_tla B.Lteq,  [U;U], SBool, [ lift_arith_predicate (m_tla B.Lteq) B.Lteq ], ["int2u"] ;
    m_tla B.Range, [U;U], U,  [
      forall [m,SInt ; n,SInt ; z,U ] (pattern_z3
      (equiv (mem z (app2 (m_tla B.Range) (int2u m) (int2u n)))
      (exists [x,SInt] (lAnd [eq z (int2u x) ; leq m x ; leq x n])))
      [ mem z (app2 (m_tla B.Range) (int2u m) (int2u n)) ])
      ;
      (** added sm 2019-02-20, fixed sm 2019-12-16:
          Range is injective when intervals are non-empty. *)
      forall [m,SInt ; n,SInt ; x,SInt ; y,SInt ]
        (implies
           (lAnd [ lOr [ leq m n ;
                         leq x y ] ;
                   (eq (app2 (m_tla B.Range) (int2u m) (int2u n))
                       (app2 (m_tla B.Range) (int2u x) (int2u y))) ])
           (lAnd [eq m x ; eq n y]))
      ;
      (** added sm 2019-02-22: Range is empty iff the upper bound is
          greater than the lower bound. *)
      forall [m,SInt ; n,SInt ]
        (equiv
           (eq (app2 (m_tla B.Range) (int2u m) (int2u n)) "tla__emptyset")
           (lt n m))
      ], [m_tla B.Mem ; "int2u" ; "tla__emptyset"] ;
    m_tla B.Uminus,[U], U,    [ forall [n,SInt] (pattern
      (eq (app1 (m_tla B.Uminus) (int2u n))
          (int2u (m_uminus smap n)))
      [ app1 (m_tla B.Uminus) (int2u n) ]) ], ["int2u"] ;
    "boolify", [U], SBool, [], [] ;
    (* m_tla B.BOOLEAN, [], U, [ forall [x,U] (equiv (mem x (m_tla B.BOOLEAN)) (lOr [app1 "boolify" x ; neg (app1 "boolify" x)])) ], ["boolify"] ; *)
    (* m_tla B.BOOLEAN, [], U, [ forall [x,U]
                   ], ["boolify"] ; *)

    (* forall x:U. mem x BOOLEAN => bool2u (boolify x) = x *)
    m_tla B.BOOLEAN, [], U, [
        forall [x,U] (pattern
            (implies (mem x (m_tla B.BOOLEAN)) (eq (bool2u (boolify x)) x))
            [ mem x (m_tla B.BOOLEAN) ]);
        (* forall [x,U] (equiv
                (mem x (m_tla B.BOOLEAN))
                (lOr [boolify x ; neg (boolify x)]) ) ; *)
             ], ["boolify"; "bool2u"] ;

    (** CHANGED equiv for two implies *)
    (* m_tla B.BOOLEAN, [], U, [
      forall [x,U] (pattern
        (implies (app1 "boolify" x) (mem x (m_tla B.BOOLEAN)))
        [ mem x (m_tla B.BOOLEAN) ]) ;
      forall [x,U] (pattern
        (implies (neg (app1 "boolify" x)) (mem x (m_tla B.BOOLEAN)))
        [ mem x (m_tla B.BOOLEAN) ]) ;
      forall [x,U] (pattern
        (implies
        (mem x (m_tla B.BOOLEAN))
        (lOr [app1 "boolify" x ; neg (app1 "boolify" x)]))
        [mem x (m_tla B.BOOLEAN)] )
      (* forall [x,U] (equiv
             (mem x (m_tla B.BOOLEAN))
             (lOr [equiv (app1 "boolify" x) (smap.op B.TRUE) ;
                   equiv (app1 "boolify" x) (smap.op B.FALSE)]))  *)
             ], ["boolify"] ; *)
    m_tla B.STRING, [], U, [], [] ;
    (* m_tla B.Mem, [U;U], SBool, [], [] ; *)
    m_tla B.Mem,    [U;U], SBool, [
        forall [s,U ; t,U] (implies
            (forall [x,U] (equiv (mem x s) (mem x t))) (eq s t))
        ], [] ;   (** with set extensionality *)
    m_tla B.Subseteq, [U;U], SBool, [
        forall [x,U;y,U] (implies
            (app2 (m_tla B.Subseteq) x y)
            (forall [z,U] (implies (mem z x) (mem z y))))
        ], [m_tla B.Mem] ;
    m_tla B.SUBSET, [U], U, [
        forall [s,U;t,U] (implies
            (mem s (app1 (m_tla B.SUBSET) t))
            (forall [x,U] (implies (mem x s) (mem x t))))
        ], [m_tla B.Mem] ;
    m_tla B.UNION, [U], U, [
        forall [x,U;s,U] (implies
            (mem x (app1 (m_tla B.UNION) s))
            (exists [t,U] (lAnd [mem t s ; mem x t])))
        ], [m_tla B.Mem] ;
    m_tla B.Cap, [U;U], U, [
        forall [x,U;s,U;t,U] (implies
            (mem x (app2 (m_tla B.Cap) s t))
            (lAnd [mem x s ; mem x t]))
        ], [m_tla B.Mem] ;
    m_tla B.Cup, [U;U], U, [
        forall [x,U;s,U;t,U] (implies
            (mem x (app2 (m_tla B.Cup) s t))
            (lOr [mem x s ; mem x t]))
        ], [m_tla B.Mem] ;
    m_tla B.Setminus, [U;U], U, [
        forall [x,U;s,U;t,U] (implies
            (mem x (app2 (m_tla B.Setminus) s t))
            (lAnd [mem x s ; neg (mem x t)]))
        ], [m_tla B.Mem] ;
    "tla__emptyset", [], U, [
        forall [x,U] (pattern
            (equiv (mem x "tla__emptyset") (smap.op B.FALSE))
            [mem x "tla__emptyset"])
        ], [m_tla B.Mem] ;
    "tla__set_1", [U], U, [
        forall [x,U;y,U] (equiv
            (mem x (app "tla__set_1" [y])) (eq x y))
        ], [m_tla B.Mem] ;
    "tla__set_2", [U;U], U, [
        forall [x,U;y,U;z,U] (equiv
            (mem x (app "tla__set_2" [y;z])) (lOr [eq x y; eq x z]))
        ], [m_tla B.Mem] ;
    "tla__isAFcn",    [U], SBool, [], [] ;
      (* forall [x,U ; y,U] (implies (lAnd [ app1 "tla__isAFcn" x ; app1 "tla__isAFcn" y ; eq x y ])
                                  (lAnd [ eq (dom x) (dom y) ;
                                          forall [z,U] (implies (mem z (dom x))
                                                                (eq (fcnapp1 x z) (fcnapp1 y z))) ])) ], [m_tla B.DOMAIN;Smt.fcnapp] ; *)
    m_tla B.DOMAIN, [U], U, [
      (** Instance of set extensionality for DOMAIN *)
      forall [f,U ; g,U] (pattern_z3 (implies
        (lAnd [ app1 "tla__isAFcn" f ; app1 "tla__isAFcn" g ;
                forall [x,U] (equiv (mem x (dom f)) (mem x (dom g))) ])
        (eq (dom f) (dom g)) )
      [ app1 "tla__isAFcn" f ; app1 "tla__isAFcn" g ] ) ;
      (** (An instance of) DOMAIN extensionality. Required, for instance, in Inv proof of Paxos. *)
      (* forall [s,U ; t,U] (equiv (eq (dom s) t) (forall [x,U] (equiv (mem x (dom s)) (mem x t)))) ; *)
      (* forall [x,U ; y,U]
        (implies
          (forall [z,U] (equiv (mem z (dom x)) (mem z (dom y))))
          (eq (dom x) (dom y))) ;   (** DOMAIN extensionality *) *)
      ], [ m_tla B.Mem ; Smt.fcnapp ; "tla__isAFcn" ] ;
    Smt.fcnapp, [U;U], U, [
      (** Function extensionality *)
      (** CHECK: what about when f and g return a Boolean? *)
      forall [f,U ; g,U] (pattern_z3 (implies
        (lAnd [ app1 "tla__isAFcn" f ; app1 "tla__isAFcn" g ;
                eq (dom f) (dom g) ;
                forall [x,U] (implies
                  (mem x (dom g))
                  (eq (fcnapp1 f x) (fcnapp1 g x))) ])
        (eq f g))
        [ app1 "tla__isAFcn" f ; app1 "tla__isAFcn" g ] ) ;
      ], [ m_tla B.Mem ; m_tla B.DOMAIN ; "tla__isAFcn" ] ;
    "tla__unspec", [U;U], U, [], [] ;
    "tla__Dot", [U;SStr], U,  [], [] ;
    "tla__fcnapp_i", [U;U], SInt,  [
      forall [x,U ; y,U] (implies
        (exists [n,SInt] (eq (app2 "tla__fcnapp_i" x y) n))
        (eq (int2u (app2 "tla__fcnapp_i" x y)) (fcnapp1 x y)))
      ], [Smt.fcnapp;"int2u"] ;
    "fcnapp1_s", [U;U], SStr,  [], [] ;
    (* "fcnapp1_i", [U;U], SInt, [], [] ; *)
    "fcnapp1_i", [U;U], SInt,  [
      forall [x,U ; y,U] (implies
        (exists [n,SInt] (eq (app2 "fcnapp1_i" x y) n))
        (eq (int2u (app2 "fcnapp1_i" x y)) (fcnapp1 x y)))
        ], [(* "isint"; *)Smt.fcnapp;"int2u"] ;
    (* "fcnapp1_i", [U;U], SInt,  [ forall [x,U ; y,U ; n,SInt] (implies (eq (app2 "fcnapp1_i" x y) n) (eq (int2u (app2 "fcnapp1_i" x y)) (fcnapp1 x y))) ], ["isint";Smt.fcnapp;"int2u"] ; *)
    (* "fcnapp1_i", [U;U], SInt,  [ forall [x,U ; y,U] (implies (isint ((app2 "fcnapp1_i" x y))) (eq (int2u (app2 "fcnapp1_i" x y)) (fcnapp1 x y))) ], ["isint";Smt.fcnapp;"int2u"] ; *)
    (* "fcnapp1_i", [U;U], SInt,  [ forall [x,U ; y,U] (eq (fcnapp1 x y) (int2u (app2 "fcnapp1_i" x y))) ], [Smt.fcnapp;"int2u"] ; *)
    "op_app1_u", [U;U], U,  [], [] ;
    "op_app1_i", [U;U], SInt,  [], [] ;
    "op_app1_s", [U;U], SStr,  [], [] ;
    (* "tla_dot_u", [U;SField], U, [], [] ; *)
    (* "tla_dot_i", [U;SField], SInt, [], [] ; *)
    (* "tla_dot_s", [U;SField], SStr, [], [] ; *)
    (* "isFldOf",   [SField;U], SBool, [ forall [m,SField ; x,U ; y,U] (implies (lAnd [ app2 "isFldOf" m y ; eq x y ]) (app2 "isFldOf" m x))  ], [] ; *)
    (* "isFldOf",   [SStr;U], SBool, [ forall [m,SStr ; x,U ; y,U] (implies (lAnd [ app2 "isFldOf" m y ; eq x y ]) (app2 "isFldOf" m x))  ], [] ; *)
    (* "tla_dot_b", [U;SField], SBool, [], [] ; *)

    "tla__tuple0", [], U, [
            (* eq (dom "tla__tuple0") "tla__emptyset" ;
            eq (app (m_tla B.Len) ["tla__tuple0"]) "0" ; *)
            forall [s,U] (equiv (eq s "tla__tuple0") (eq (dom s) "tla__emptyset")) ;    (* The empty tuple is the only function whose domain is the empty set. *)
            forall [s,U] (equiv (eq s "tla__tuple0") (eq (app (m_tla B.Len) [s]) "0")) ;
      ], [m_tla B.Mem ; m_tla B.DOMAIN ; "tla__emptyset" ; m_tla B.Len] ;

    m_tla B.Seq,       [U], U, [
            (* forall [s,U ; t,U] (implies (mem s (app1 "Seq" t)) (eq (dom s) (app2 "tla__Range" (int2u "1") (int2u (app (m_tla B.Len) [s]))))) ; *)
        forall [s,U ; t,U] (
            equiv
            (mem s (app1 (m_tla B.Seq) t))
          (lAnd [
            leq "0" (app1 (m_tla B.Len) s) ;
            app1 "tla__isAFcn" s ;
            eq (dom s) (app2 (m_tla B.Range) (int2u "1") (int2u (app (m_tla B.Len) [s]))) ;
            forall [i,SInt] (implies
                (lAnd [leq "1" i ; leq i (app (m_tla B.Len) [s])])
                (mem (fcnapp1 s (int2u i)) t)) ;
            ])) ],
        [m_tla B.Len ; m_tla B.DOMAIN ; Smt.fcnapp ; "int2u" ; "tla__isAFcn" ; m_tla B.Range] ;

    m_tla B.Len, [U], SInt, [
        forall [s,U;n,SInt] (implies (leq "0" n) (equiv
            (eq (dom s) (app2 (m_tla B.Range) (int2u "1") (int2u n)))
        (eq (app1 (m_tla B.Len) s) n))) ;
      forall [s,U] (leq "0" (app1 (m_tla B.Len) s))
      ], [m_tla B.DOMAIN;m_tla B.Range;"int2u"] ;

    m_tla B.SubSeq,    [U;U;U], U, [], [] ;
    m_tla B.Head,      [U], U, [], [] ;
    m_tla B.Tail,      [U], U, [], [] ;
    m_tla B.BSeq,      [U], U, [], [] ;
    m_tla B.Cat,       [U;U], U, [], [] ;
    m_tla B.Append,    [U;U], U, [], [] ;
    m_tla B.SelectSeq, [U;U], U, [], [] ;
    m_tla B.Infinity,  [], SInt, [], [] ;
    ]
    (* @
    (** Tuples *)
    map (fun ts ->
        let mki i = "X__"^(string_of_int (i+1)) in
        let vs = mapi (fun i _ -> mki i, U) ts in
        (* let nts = combine ns ts in *)
        let t_id = sprintf "tuple_%s" (String.concat "" (map (function _ -> "u") ts)) in
        (* let t_id = sprintf "tuple_%s" (String.concat "" (map (function Int -> "i" | _ -> "u") ts)) in *)
        (* let vs = map (fun (i,t) -> "x__"^i, t) nts in *)
        let es = mapi (fun i _ -> mki i) ts in
        (* let es2 = map (fun (i,t) -> if t = SInt then int2u ("x__"^i) else "x__"^i) nts in *)
        (* let nts = filter (fun (_,t) -> match t with SInt -> true | _ -> false) nts in *)
            t_id,
            (* ts,  *) map (fun _ -> U) ts,
            U,
            mapi (fun i _ -> forall vs (eq (mki i) (fcnapp1 (app t_id es) (int2u (string_of_int (i+1)))))) ts
            (* map (fun (i,t) -> forall vs (eq ("x__"^i) (app2 (match t with SInt -> "fcnapp1_i" | _ -> Smt.fcnapp) (app t_id es) (int2u i)))) nts, *)
            @ begin if !Smt.mode = Smt.Spass then
            mapi (fun i t ->
                forall vs (eq (mki i)
                              begin match t with Int -> int2u (app2 "fcnapp1_i" (app t_id es) (int2u (string_of_int (i+1))))
                                               | _ -> "" (* app2 Smt.fcnapp (app t_id es) (int2u i) *) end)) ts
              else [] end
            ,
            ["int2u";Smt.fcnapp] @ (if !Smt.mode = Smt.Spass then ["fcnapp1_i"] else []) )
        tuples
        *)
    (* @
    (** Records *)
    (* List.concat *)
    begin map (fun (fs,id) ->
        let mkx f = "X__"^f in
        let r_id = sprintf "tla__record__%d" (Smt.get_recid fs) in
        (* let fields = map add_field_prefix fields in *)
        let vs = map (fun f -> mkx f, U) fs in
        let xs = map mkx fs in
        (* add_extrasort "tla_Field" ; *)
        r_id, List.mapi (fun _ _ -> U) fs, U,
           (* [ forall ((x,U)::vs) (equiv (eq x (app r_id es)) (lAnd (map (fun f -> eq (app "tla_dot_u" [x ; f]) ("x__"^f)) fields)))   (*** record extensionality *)
            ] @ *)
            begin forall ((x,U)::vs)
              (equiv
                (mem x (dom (app r_id xs)))
                (lOr (map (fun f -> eq x (str2u (Smt.mk_string f))) fs)))
            end ::
            (* begin forall vs
              (lAnd (map (fun f -> mem (str2u (Smt.mk_string f)) (dom (app r_id xs))) fs))
            end :: *)
            begin
              map (fun f ->
                forall vs (eq (fcnapp1 (app r_id xs) (str2u (Smt.mk_string f))) (mkx f))
                ) fs
            end,
            [Smt.fcnapp;"str2u"]
        ) (Smt.SSMap.bindings !Smt.record_ids)
    end *)
  in
  (* let std_set = if !Smt.record_signatures <> [] then std_set else std_set
    @ [ "tla__isAFcn" ; m_tla B.Mem ; Smt.fcnapp ]
    @ (map (fun hs -> "tla__set_"^(string_of_int (List.length hs)))
        !Smt.record_signatures)
  in *)

  (** Add dependencies to set of standard operators *)
  let rec fixp_add_deps std_set =
    let ff oops =
      let deps = List.fold_left
        (fun r (o,_,_,_,deps) -> if List.mem o oops then deps @ r else r)
        [] all_std_ops
      in
      Smt.remove_repeated (deps @ oops)
    in
    let ops' = ff std_set in
    if std_set = ops' then std_set else fixp_add_deps ops'
  in
  let std_set = fixp_add_deps std_set in

  let std = List.filter (fun (id,_,_,_,_) -> List.mem id std_set) all_std_ops in

  (** Add SetEnum operators "tla__set_n" to [std] *)
  let std =
    (** setenums = list [n1; ... ; nn] from required "tla__set_n" operators *)
    let setenums = List.fold_left (fun r (op,_,_,_,_) ->
(* Util.eprintf "op == %s" op ; *)
      if Str.string_match (Str.regexp "tla__set_\\([0-9].*\\)") op 0 then (
(* Util.eprintf "op == %s --> %s" op (Str.matched_group 1 op) ; *)
        (int_of_string (Str.matched_group 1 op)) :: r) else r
      ) [] std
    in
    if setenums = [] then std else std
    @ (map begin fun n ->
        let xs = map (fun _ -> "X_"^Smt.fresh_id ()) (Smt.n_to_list n) in
        let axiom = forall ((y,U) :: (map (fun x -> x,U) xs)) (implies
            (mem y (app ("tla__set_"^(string_of_int n)) xs))
            (lOr (map (fun x -> eq y x) xs)) )
        in
        ("tla__set_"^(string_of_int n), (map (fun _ -> U) xs), U, [axiom], [m_tla B.Mem])
      end setenums)
  in

  (** Already added in pre-processing *)
  (* let rec_ext_axioms = !Smt.record_signatures
    |> List.filter (fun hs -> hs <> [])
    |> Smt.remove_repeated
    |> map begin fun hs ->
        let n = List.length hs in
        let hs = map (fun h -> (str2u (Smt.mk_string h))) hs in
        (* let mk_dom_ext x hs = forall [i,U] (equiv (mem i (dom x)) (lAnd (map (eq i) hs))) in *)
        forall [x,U ; y,U] (implies
          (lAnd (
            (app1 "tla__isAFcn" x) :: (app1 "tla__isAFcn" y) ::
            (* (eq (dom x) (dom y)) :: *)
            (* (mk_dom_ext x hs) :: *)
            (* (mk_dom_ext y hs) :: *)
            (eq (dom x) (app ("tla__set_"^(string_of_int n)) hs)) ::
            (map (fun h -> eq (fcnapp1 x h) (fcnapp1 y h)) hs)))
          (eq x y))
      end
  in *)

  let axioms = List.concat (map (fun (_,_,_,a,_) -> a) std) in
  (* let axioms = axioms @ rec_ext_axioms in *)

  let std = (map (fun (a,b,c,_,_) -> (a,b,c)) std) in
  std,axioms
