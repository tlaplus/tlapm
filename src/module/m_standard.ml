(* Standard TLA+ modules.

Copyright (C) 2008-2010  INRIA and Microsoft Corporation
*)
open Ext
open Property
open Util.Coll

open Expr.T

open M_t

module B = Builtin


let stloc =
  { Loc.file = "<StandardModules>" ;
    Loc.start = Loc.dummy ;
    Loc.stop = Loc.dummy }

let stm x = Util.locate x stloc
let st = stm ()

let nullary what op =
    let name = what @@ st in
    let op = Internal op @@ st in
    let df = Operator (name, op) @@ st in
    Definition (df, Builtin, Visible, Export) @@ st

let lambda arity name fn =
  assert (arity >= 1);
  let vars = List.init arity (fun n -> ("x" ^ string_of_int (n + 1)) @@ st, Shape_expr) in
  let lambda = Lambda (vars, fn vars) @@ st in
  Definition (Operator (name @@ st, lambda) @@ st, Builtin, Visible, Export) @@ st

let operator arity name op =
  lambda arity name begin
    fun _ -> assert (arity >= 1);
      Apply (Internal op @@ st,
             List.init arity (fun n -> Ix (arity - n) @@ st)) @@ st
  end

let unary = operator 1
let binary = operator 2
let ternary = operator 3

let naturals =
  let (_, m, _) = M_elab.normalize Sm.empty Deque.empty begin
    stm {
      name = "Naturals" @@ st ;
      extendees = [] ;
      instancees = [] ;
      defdepth = 0 ;
      important = false ;
      body = [
        nullary "Nat"   B.Nat ;
        binary  "+"     B.Plus ;
        binary  "-"     B.Minus ;
        binary  "*"     B.Times ;
        binary  "^"     B.Exp ;
        binary  "<"     B.Lt ;
        binary  ">"     B.Gt ;
        binary  "=<"    B.Lteq ;
        binary  ">="    B.Gteq ;
        binary  "%"     B.Remainder ;
        binary  "\\div" B.Quotient ;
        binary  ".."    B.Range
      ] ;
      stage = Special ;
    }
  end in
  m

let integers =
  let (_, m, _) = M_elab.normalize Sm.empty Deque.empty begin
    stm {
      name = "Integers" @@ st ;
      extendees = [] ;
      instancees = [] ;
      defdepth = 0 ;
      important = false ;
      body = naturals.core.body @ [
        nullary "Int" B.Int ;
        unary   "-."  B.Uminus
      ] ;
      stage = Special ;
    }
  end in
  m

let reals =
  let (_, m, _) = M_elab.normalize Sm.empty Deque.empty begin
    stm {
      name = "Reals" @@ st ;
      extendees = [] ;
      instancees = [] ;
      defdepth = 0 ;
      important = false ;
      body = integers.core.body @ [
        nullary "Real"     B.Real ;
        binary  "/"        B.Ratio ;
        nullary "Infinity" B.Infinity ;
      ] ;
      stage = Special ;
    }
  end in
  m

let sequences =
  let (_, m, _) = M_elab.normalize Sm.empty Deque.empty begin
    stm {
      name = "Sequences" @@ st ;
      extendees = [] ;
      instancees = [] ;
      defdepth = 0 ;
      important = false ;
      body = [
        unary   "Seq"       B.Seq ;
        unary   "Len"       B.Len ;
        binary  "BSeq"      B.BSeq ;
        binary  "\\o"       B.Cat ;
        binary  "Append"    B.Append ;
        unary   "Head"      B.Head ;
        unary   "Tail"      B.Tail ;
        ternary "SubSeq"    B.SubSeq ;
        binary  "SelectSeq" B.SelectSeq
      ] ;
      stage = Special ;
    }
  end in
  m

let tlc =
  let (_, m, _) = M_elab.normalize Sm.empty Deque.empty begin
    stm {
      name = "TLC" @@ st ;
      extendees = [] ;
      instancees = [] ;
      defdepth = 0 ;
      important = false ;
      body = [
        binary  "Print"         B.Print ;
        unary   "PrintT"        B.PrintT ;
        binary  "Assert"        B.Assert ;
        nullary "JavaTime"      B.JavaTime ;
        unary   "TLCGet"        B.TLCGet ;
        binary  "TLCSet"        B.TLCSet ;
        binary  ":>"            B.OneArg ;
        binary  "@@"            B.Extend ;
        unary   "Permutations"  B.Permutations ;
        binary  "SortSeq"       B.SortSeq ;
        unary   "RandomElement" B.RandomElement ;
        nullary "Any"           B.Any ;
        unary   "ToString"      B.ToString ;
      ] ;
      stage = Special ;
    }
  end in
  m

let tlapm =
  let (_, m, _) = M_elab.normalize Sm.empty Deque.empty begin
    stm {
      name = "$TLAPM" @@ st ;
      extendees = [] ;
      instancees = [] ;
      defdepth = 0 ;
      important = false ;
      body = [
        (* logic *)
        nullary "Builtins!True"          B.TRUE ;
        nullary "Builtins!False"         B.FALSE ;
        binary  "Builtins!Implies"       B.Implies ;
        binary  "Builtins!Equiv"         B.Equiv ;
        binary  "Builtins!Conj"          B.Conj ;
        binary  "Builtins!Disj"          B.Disj ;
        unary   "Builtins!Neg"           B.Neg ;
        binary  "Builtins!Eq"            B.Eq ;
        binary  "Builtins!Neq"           B.Neq ;
        (* set theory *)
        nullary "Builtins!String"        B.STRING ;
        nullary "Builtins!Boolean"       B.BOOLEAN ;
        unary   "Builtins!Subset"        B.SUBSET ;
        unary   "Builtins!Union"         B.UNION ;
        unary   "Builtins!Domain"        B.DOMAIN ;
        binary  "Builtins!Subseteq"      B.Subseteq ;
        binary  "Builtins!Mem"           B.Mem ;
        binary  "Builtins!Notmem"        B.Notmem ;
        binary  "Builtins!Setminus"      B.Setminus ;
        binary  "Builtins!Cap"           B.Cap ;
        binary  "Builtins!Cup"           B.Cup ;
        (* modal *)
        unary   "Builtins!Prime"         B.Prime ;
        binary  "Builtins!Leadsto"       B.Leadsto ;
        unary   "Builtins!Enabled"       B.ENABLED ;
        unary   "Builtins!Unchanged"     B.UNCHANGED ;
        binary  "Builtins!Cdot"          B.Cdot ;
        binary  "Builtins!Actplus"       B.Actplus ;
        unary   "Builtins!Box"           (B.Box true) ;
        unary   "Builtins!Diamond"       B.Diamond ;
        (* arithmetic *)
        nullary "Builtins!Nat"           B.Nat ;
        nullary "Builtins!Int"           B.Int ;
        nullary "Builtins!Real"          B.Real ;
        binary  "Builtins!Plus"          B.Plus ;
        binary  "Builtins!Minus"         B.Minus ;
        unary   "Builtins!Uminus"        B.Uminus ;
        binary  "Builtins!Times"         B.Times ;
        binary  "Builtins!Ratio"         B.Ratio ;
        binary  "Builtins!Quotient"      B.Quotient ;
        binary  "Builtins!Remainder"     B.Remainder ;
        binary  "Builtins!Exp"           B.Exp ;
        nullary "Builtins!Infinity"      B.Infinity ;
        binary  "Builtins!Lteq"          B.Lteq ;
        binary  "Builtins!Lt"            B.Lt ;
        binary  "Builtins!Gteq"          B.Gteq ;
        binary  "Builtins!Gt"            B.Gt ;
        binary  "Builtins!Range"         B.Range ;
        (* sequences *)
        unary   "Builtins!Seq"           B.Seq ;
        unary   "Builtins!Len"           B.Len ;
        binary  "Builtins!Bounded"       B.BSeq ;
        binary  "Builtins!Cat"           B.Cat ;
        binary  "Builtins!Append"        B.Append ;
        unary   "Builtins!Head"          B.Head ;
        unary   "Builtins!Tail"          B.Tail ;
        ternary "Builtins!Subseq"        B.SubSeq ;
        binary  "Builtins!Select"        B.SelectSeq ;
        (* tlc *)
        binary  "Builtins!Single"        B.OneArg ;
        binary  "Builtins!Join"          B.Extend ;
        binary  "Builtins!Print"         B.Print ;
        unary   "Builtins!PrintT"        B.PrintT ;
        binary  "Builtins!Assertion"     B.Assert ;
        nullary "Builtins!JavaTime"      B.JavaTime ;
        unary   "Builtins!TLCGet"        B.TLCGet ;
        binary  "Builtins!TLCSet"        B.TLCSet ;
        unary   "Builtins!Permutations"  B.Permutations ;
        binary  "Builtins!SortSeq"       B.SortSeq ;
        unary   "Builtins!RandomElement" B.RandomElement ;
        nullary "Builtins!Any"           B.Any ;
        unary   "Builtins!ToString"      B.ToString ;
      ] ;
      stage = Special ;
    }
  end in
  m

(** create a map between the name of the standard modules and (the wrappers of) the modules*)
let initctx =
  List.fold_left
    (fun mx m -> Sm.add m.core.name.core m mx)
    Sm.empty
    [ naturals ; integers ; reals ; sequences ; tlc ; tlapm ]
