(* method_prs.ml --- parse method pragmas
 *
 *
 * Copyright (C) 2008-2019  INRIA and Microsoft Corporation
 *)

(* FIXME we should remove this way of specifying methods and instead use
   the new (*{ by (prover: "foo"; timeout: x) }*) syntax. *)

open Ext

open Method

open Tla_parser.P

open Tla_parser

let float =
  number <$> (fun (m, n) -> float_of_string (Printf.sprintf "%s.%s" m n))

let rec read_method = lazy begin
  pragma (ident "by" >>> use isa_method)
end

and isa_method = lazy begin
  punct "(" >>>
    choice [ use isa_gen ;
             use isa_zenon ;
             isa_smt ;
             isa_cvc3 ;
             isa_yices ;
             isa_z3 ;
             isa_cooper ;
             isa_fail ;
             isa_smt2lib;
             isa_smt2z3;
             isa_smt3;
             isa_z33;
             isa_cvc33;
             isa_yices3;
             isa_verit;
             isa_zipper;
             isa_spass;
             isa_tptp;
             isa_ls4;
             isa_enabled;
             isa_cdot;
             isa_autouse;
             isa_lambdify;
             isa_enabledaxioms;
             isa_enabledrewrites;
             isa_enabledrules;
             isa_levelcomparison;
             isa_trivial;
           ]
  <<< punct ")"
end

and isa_gen = lazy begin
  ident "isabelle" >>>
     (str) <*> optional float
    <$> (fun (tac,tio) ->
           let tio = Option.default default_isabelle_timeout tio in
           Isabelle (tio, tac)
       )
end

(* FIXME remove "fallback" syntax; for now it is simply ignored *)
and isa_zenon = lazy begin
  ident "zenon" >>>
    optional float <*> optional (use isa_method)
    <$> (fun (tout, fb) ->
           let tout = Option.default default_zenon_timeout tout in
             Zenon tout)
end

and isa_smt =
  ident "smt" <!> Smt3 default_smt_timeout

and isa_cvc3 =
  ident "cvc3" <!> Cvc33 default_cvc3_timeout

and isa_yices =
  ident "yices" <!> Yices3 default_yices_timeout

and isa_z3 =
  ident "z3" <!> Z33 default_z3_timeout

and isa_ls4 =
  ident "ls4" <!> LS4 default_ls4_timeout

and isa_cooper =
  (ident "cooper" <|> ident "presburger") <!> Cooper
(* FIXME remove presburger alias *)
(* FIXME remove also cooper *)

and isa_fail =
  ident "fail" <!> Fail

and isa_smt2lib = ident "smt2lib" <!> Smt3 default_smt2_timeout

and isa_smt2z3 = ident "smt2z3" <!> Z33 default_smt2_timeout

and isa_smt3 = ident "smt3" <!> Smt3 default_smt2_timeout

and isa_z33 = ident "z33" <!> Z33 default_smt2_timeout

and isa_cvc33 = ident "cvc33" <!> Cvc33 default_smt2_timeout

and isa_yices3 = ident "yices3" <!> Yices3 default_smt2_timeout

and isa_verit = ident "verit" <!> Verit default_smt2_timeout

and isa_zipper = ident "zipper" <!> Zipper default_zipper_timeout

and isa_spass = ident "spass" <!> Spass default_spass_timeout

and isa_tptp = ident "tptp" <!> Tptp default_tptp_timeout

and isa_enabled = ident "expandenabled" <!> ExpandENABLED

and isa_cdot = ident "expandcdot" <!> ExpandCdot

and isa_autouse = ident "autouse" <!> AutoUSE

and isa_lambdify = ident "lambdify" <!> Lambdify

and isa_enabledaxioms = ident "enabledaxioms" <!> ENABLEDaxioms

and isa_enabledrewrites = ident "enabledrewrites" <!> ENABLEDrewrites

and isa_enabledrules = ident "enabledrules" <!> ENABLEDrules

and isa_levelcomparison = ident "levelcomparison" <!> LevelComparison

and isa_trivial = ident "trivial" <!> Trivial
