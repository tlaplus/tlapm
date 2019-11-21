(*
 * alexer.mli --- lexer interface
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** The lexer *)

open Pars
open Tla_parser

(** Lex a channel *)
val lex_channel :
  string -> Pervasives.in_channel -> Token.token LazyList.t * Loc.locus

(** Main lexing function *)
val lex : string -> Token.token LazyList.t * Loc.locus

(** For debugging: lexing function that takes a string as input.
    NOTE: does not handle the beginning-of-file stuff.
*)
val lex_string : string -> Token.token LazyList.t * Loc.locus;;
