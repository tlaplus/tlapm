(*
 * method_old.ml --- abstraction of methods : old version to keep fingerprints compatibility
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev$";;

open Ext

type t =
  | Isabelle of string
  | Zenon of zenon
  | Smt | Yices | Z3 | Cooper
  | Sorry (*| Fail*)


and zenon = { zenon_timeout : float ;
              zenon_fallback : t}


let default_zenon = { zenon_timeout = 10.0 ;
                      zenon_fallback = Isabelle "auto" }


type status_type = Trivial | BeingProved | Success of t | Fail of t | Checked | Interrupted of t


open Format

let rec pp_print_method ff meth =
  fprintf ff "@[<h>(*{ by %a }*)@]"
    pp_print_tactic meth

and pp_print_tactic ff = function
  | Isabelle is ->
      fprintf ff "@[<h>(%s)@]" is
  | Zenon zen ->
      fprintf ff "@[<h>(%a)@]" pp_print_zenon zen
  | Smt ->
      fprintf ff "(smt)"
  | Yices ->
      fprintf ff "(yices)"
  | Z3 ->
      fprintf ff "(z3)"
  | Cooper ->
      fprintf ff "(cooper)"
  | Sorry ->
      fprintf ff "(sorry)"
(*  | Fail ->
      fprintf ff "(fail)"*)

and pp_print_zenon ff zen =
  fprintf ff "zenon %g %a"
    zen.zenon_timeout
    pp_print_tactic zen.zenon_fallback


let pp_print_tactic_fp ff = function
  | Isabelle is ->
      fprintf ff "isabelle=%s" is
  | Zenon zen ->
      fprintf ff "zenon=%g" zen.zenon_timeout
  | Smt ->
      fprintf ff "smt= "
  | Yices ->
      fprintf ff "yices= "
  | Z3 ->
      fprintf ff "z3= "
  | Cooper ->
      fprintf ff "cooper= "
  | Sorry ->
      fprintf ff "sorry= "
(*  | Fail ->
      fprintf ff "fail= "*)
