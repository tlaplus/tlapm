(*
 * smtlib/fmt.ml -- pretty-printing
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Format
open Fmtutil

open S_t


let pp_print_symbol = pp_print_string

let pp_print_spaced f ppf xs = pp_print_delimited ~sep:pp_print_space f ppf xs

let rec pp_print_term ppf t =
  match t with
  | Literal lit -> pp_print_lit ppf lit
  | App (qid, ts) ->
      if List.length ts = 0 then
        pp_print_qual_ident ppf qid
      else
        fprintf ppf "(@[%a@ %a)@]"
        pp_print_qual_ident qid
        (pp_print_spaced pp_print_term) ts
  | Let (vbs, t) ->
      fprintf ppf "(@[let (@[%a)@]@ %a)@]"
      (pp_print_spaced pp_print_var_bind) vbs
      pp_print_term t
  | Quant (q, sbs, t) ->
      let s = match q with Forall -> "forall" | Exists -> "exists" in
      fprintf ppf "(@[%s (@[%a)@]@ %a)@]" s
      (pp_print_spaced pp_print_sorted_bind) sbs
      pp_print_term t
  | Match (t, mcs) ->
      fprintf ppf "(@[match %a@ (@[%a)@])@]"
      pp_print_term t
      (pp_print_spaced pp_print_match_case) mcs
  | Annot (t, attrs) ->
      if List.length attrs = 0 then
        pp_print_term ppf t
      else
        fprintf ppf "(@[! %a@ %a)@]"
        pp_print_term t
        (pp_print_spaced pp_print_attribute) attrs

and pp_print_lit ppf lit =
  match lit with
  | LInt n -> pp_print_int ppf n
  | LStr s -> pp_print_string ppf s

and pp_print_qual_ident ppf qid =
  match qid with
  | Id smb -> pp_print_symbol ppf smb
  | As (smb, srt) ->
      fprintf ppf "(@[as %a@ %a)@]"
      pp_print_symbol smb
      pp_print_sort srt

and pp_print_var_bind ppf (smb, t) =
  fprintf ppf "(@[%a@ %a)@]"
  pp_print_symbol smb
  pp_print_term t

and pp_print_sorted_bind ppf (smb, srt) =
  fprintf ppf "(@[%a@ %a)@]"
  pp_print_symbol smb
  pp_print_sort srt

and pp_print_match_case ppf (pat, t) =
  fprintf ppf "(@[%a@ %a)@]"
  pp_print_pattern pat
  pp_print_term t

and pp_print_sort ppf srt =
  match srt with
  | Sort (smb, ss) ->
      if List.length ss = 0 then
        pp_print_symbol ppf smb
      else
        fprintf ppf "(@[%a (@[%a)@])@]"
        pp_print_symbol smb
        (pp_print_spaced pp_print_sort) ss

and pp_print_pattern ppf (smb, smbs) =
  if List.length smbs = 0 then
    pp_print_symbol ppf smb
  else
    fprintf ppf "(@[%a (@[%a)@])@]"
    pp_print_symbol smb
    (pp_print_spaced pp_print_symbol) smbs

and pp_print_attribute ppf (smb, attrv) =
  match attrv with
  | None ->
      fprintf ppf ":%a"
      pp_print_symbol smb
  | Some attrv ->
      fprintf ppf ":%a@ %a"
      pp_print_symbol smb
      pp_print_attribute_val attrv

and pp_print_attribute_val ppf attrv =
  match attrv with
  | AttrLit lit -> pp_print_lit ppf lit
  | AttrIdent smb -> pp_print_symbol ppf smb
  | AttrList ts ->
      fprintf ppf "(@[%a)@]"
      (pp_print_spaced pp_print_term) ts

