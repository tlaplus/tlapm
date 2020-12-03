(*
 * module/parser.ml --- modules (parsing)
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Property

open Tla_parser.P
open Tla_parser

open Expr.T
open Expr.Parser

open M_t

let with_meth e meth = match meth with
  | Some meth -> { e with core = With (e, meth) }
  | None -> e

let rec modunit = lazy begin
  choice [
    choice [
      (kwd "CONSTANT" <|> kwd "CONSTANTS") >*>
        sep1 (punct ",") (use opdecl)
      <$> (fun cs -> [ Constants cs ]) ;

      (kwd "RECURSIVE") >*>
        sep1 (punct ",") (use opdecl)
      <$> (fun cs -> [ Recursives cs ]) ;

      (kwd "VARIABLE" <|> kwd "VARIABLES") >*>
        sep1 (punct ",") (locate anyident)
      <$> (fun vs -> [ Variables vs ]) ;
    ] ;

    optional (kwd "LOCAL") >>= begin fun l ->
      let ex = if Option.is_some l then Local else Export in
        choice [
          use (instance false)
          <$> (fun inst -> [ Anoninst (inst, ex) ]) ;

          use (defn false)
          <$> (fun df -> [ Definition (df, User, Hidden, ex) ]) ;
        ]
    end ;

    use Proof.Parser.suppress
    <*> (kwd "USE" <|> kwd "HIDE")
    <**> use Proof.Parser.usebody
    <$> (fun ((supp, uh), us) -> match uh with
           | "USE" -> [ Mutate (`Use (supp = Proof.Parser.Suppress), us) ]
           | _ -> [ Mutate (`Hide, us) ]) ;

    (kwd "AXIOM" <|> kwd "ASSUME" <|> kwd "ASSUMPTION") >*>
      optional (locate anyident <<< punct "==") <**> use (expr false)
    <*> optional (use Method_prs.read_method)
    <$> (fun ((nm, e), meth) -> [ Axiom (nm, with_meth e meth) ]) ;

    (kwd "THEOREM" <|> kwd "PROPOSITION" <|> kwd "COROLLARY" <|> kwd "LEMMA") >*>
      optional (locate anyident <<< punct "==")
    <*> choice [ use (sequent false) ;
                 use (expr false) <$> (fun e -> { context = Deque.empty ; active = e }) ]
    <*> optional (use Method_prs.read_method)
    <*> use Proof.Parser.proof
    <$> (fun (((nm, bod), meth), prf) ->
           [ Theorem (nm, { bod with active = with_meth bod.active meth }, 0, prf, prf, empty_summary) ]) ;

    enabled (punct "----" <*> kwd "MODULE")
      >*> use parse <$> (fun m -> [ Submod m ]) ;

    punct "----" <!> [] ;
  ]
end

and flat_locate p =
  locate p <$> fun xsw ->
    List.map (fun x -> { core = x ; props = xsw.props }) xsw.core

and modunits = lazy begin
  choice [
    flat_locate (use modunit) <::> use modunits ;
    succeed [] ;
  ]
end

and parse = lazy begin
  locate (use parse_)
end

(* submodules --- See above *)
and parse_ = lazy begin
  (punct "----" >*> kwd "MODULE" >*> locate anyname <<< punct "----")
  <*> optional (kwd "EXTENDS" >>> sep1 (punct ",") (locate anyident))
  <**> use modunits <<< punct "===="
  <$> begin fun ((nm, exs), mus) ->
    let extends = Option.default [] exs in
    { name = nm
    ; extendees = extends
    ; instancees = []
    ; defdepth = 0
    ; important = (* false *) true  (* to simplify proofs of submodules *)
    ; body = List.concat mus
    ; stage = Parsed }
  end
end
