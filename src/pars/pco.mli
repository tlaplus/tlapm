(*
 * pars/pco.mli --- Combinator parsing
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** The combinator parsing library *)

(** Build an implementation of a parser parameterised on the token and
    precedence types. *)
module type Make_sig = sig

  (* Functor arguments, reexported *)
  module Tok : Intf.Tok
  module Prec : Intf.Prec

  (*
   * type tokus = (Tok.token * Tok.token) option
   * val locus : ?last:Tok.token -> tokus -> Loc.locus
   *)

  (** The type [('s, 'a) prs] represents parsers with internal (user)
      state of type ['s] returning results of type ['a] *)
  type ('s, 'a) prs

  (** Run the given parser on the given token stream, returning a
      possible parsed value. On success, the input contains the
      unparsed suffix. On failure, the input is left untouched. *)
  val run :
    ('s, 'a) prs ->
    init:'s ->
    source:Tok.token LazyList.t ->
    'a option

  (** {2 Primitive parsers} *)

  (** [return a] immediately succeeds with [a], consuming no input *)
  val return : 'a -> Loc.locus -> ('s, 'a) prs

  val succeed : 'a -> ('s, 'a) prs

  val fail : string -> ('s, 'a) prs

  val debug : string -> ('s, unit) prs

  val report : ?verb:int -> string -> ('s, 'a) prs -> ('s, 'a) prs

  val explain : string -> ('s, 'a) prs -> ('s, 'a) prs

  val withloc : ('s, 'a) prs -> ('s, 'a * Loc.locus) prs

  (** {2 State operations} *)

  val get : ('s, 's) prs

  val put : 's -> ('s, unit) prs

  val morph : ('s -> 's) -> ('s, unit) prs

  val using : 's -> ('s, 'a) prs -> ('s, 'a) prs

  (** {2 Delay} *)

  val use : ('s, 'a) prs Lazy.t -> ('s, 'a) prs

  val thunk : (unit -> ('s, 'a) prs) -> ('s, 'a) prs

  (* val ( @@ ) : ('a -> ('s, 'b) prs) -> 'a -> ('s, 'b) prs *)

  (** {2 Primitive combinators} *)

  val ( >>+ ) : ('s, 'a) prs -> ('a -> Loc.locus -> ('s, 'b) prs) -> ('s, 'b) prs

  val ( <|> ) : ('s, 'a) prs -> ('s, 'a) prs -> ('s, 'a) prs

  val ( <*>  ) : ('s, 'a) prs -> ('s, 'b) prs -> ('s, 'a * 'b) prs

  val commit : ('s, 'a) prs -> ('s, 'a) prs

  (** {2 Derived combinators} *)

  val ( <**> ) : ('s, 'a) prs -> ('s, 'b) prs -> ('s, 'a * 'b) prs

  val ( >>= ) : ('s, 'a) prs -> ('a -> ('s, 'b) prs) -> ('s, 'b) prs

  val ( >>> ) : ('s, 'a) prs -> ('s, 'b) prs -> ('s, 'b) prs

  val ( >*> ) : ('s, 'a) prs -> ('s, 'b) prs -> ('s, 'b) prs

  val ( <<< ) : ('s, 'a) prs -> ('s, 'b) prs -> ('s, 'a) prs

  val ( <$> ) : ('s, 'a) prs -> ('a -> 'b) -> ('s, 'b) prs

  val ( <!> ) : ('s, 'a) prs -> 'b -> ('s, 'b) prs

  val ( <?> ) : ('s, 'a) prs -> ('a -> bool) -> ('s, 'a) prs

  val ( <$?> ) : ('s, 'a) prs -> ('a -> 'b option) -> ('s, 'b) prs

  val ( <::> ) : ('s, 'a) prs -> ('s, 'a list) prs -> ('s, 'a list) prs

  val ( <@>  ) : ('s, 'a list) prs -> ('s, 'a list) prs -> ('s, 'a list) prs

  (** {2 Infinite lookahead parsers} *)

  val lookahead : ('s, 'a) prs -> ('s, 'a) prs

  val enabled : ('s, 'a) prs -> ('s, unit) prs

  val disabled : ('s, 'a) prs -> ('s, unit) prs

  val attempt : ('s, 'a) prs -> ('s, 'a) prs

  val optional : ('s, 'a) prs -> ('s, 'a option) prs

  (** {2 Alternation} *)

  val choice : ('s, 'a) prs list -> ('s, 'a) prs

  val alt : ('s, 'a) prs list -> ('s, 'a) prs

  (** {2 Sequence parsers} *)

  val seq : ('s, 'a) prs list -> ('s, 'a list) prs

  val ix : (int -> ('s, 'a) prs) -> ('s, 'a list) prs

  (** {2 Kleene star} *)

  val star : ('s, 'a) prs -> ('s, 'a list) prs

  val star1 : ('s, 'a) prs -> ('s, 'a list) prs

  val sep : ('s, 'sep) prs -> ('s, 'a) prs -> ('s, 'a list) prs

  val sep1 : ('s, 'sep) prs -> ('s, 'a) prs -> ('s, 'a list) prs

  (** {2 Token parsers} *)

  (* val peek : ('s, Tok.token option) prs *)

  val scan : (Tok.token -> 'a option) -> ('s, 'a) prs

  val satisfy : (Tok.token -> bool) -> ('s, Tok.token) prs

  val any : ('s, Tok.token) prs

  val literal : Tok.token -> ('s, unit) prs

  val string : Tok.token list -> ('s, unit) prs

  (** {2 Precedence resolution} *)

  type assoc = Left | Right | Non

  type 'a item =
    | Atm of 'a
    | Opr of Prec.prec * 'a opr

  and 'a opr =
    | Prefix of (Loc.locus -> 'a -> 'a)
    | Postfix of (Loc.locus -> 'a -> 'a)
    | Infix of assoc * (Loc.locus -> 'a -> 'a -> 'a)

  val resolve : (bool -> ('s, 'a item list) prs) -> ('s, 'a) prs

  (** {2 Lifts} *)

  val lift1 :
    ('a -> 'b) ->
    ('s, 'a) prs -> ('s, 'b) prs

  val lift2 :
    ('a -> 'b -> 'c) ->
    ('s, 'a) prs -> ('s, 'b) prs -> ('s, 'c) prs

  val lift3 :
    ('a -> 'b -> 'c -> 'd) ->
    ('s, 'a) prs -> ('s, 'b) prs -> ('s, 'c) prs -> ('s, 'd) prs

  val lift4 :
    ('a -> 'b -> 'c -> 'd -> 'e) ->
    ('s, 'a) prs -> ('s, 'b) prs -> ('s, 'c) prs -> ('s, 'd) prs -> ('s, 'e) prs

  val lift5 :
    ('a -> 'b -> 'c -> 'd -> 'e -> 'f) ->
    ('s, 'a) prs -> ('s, 'b) prs -> ('s, 'c) prs -> ('s, 'd) prs -> ('s, 'e) prs -> ('s, 'f) prs
end

module Make (Tok : Intf.Tok) (Prec : Intf.Prec) :
  Make_sig with module Tok = Tok and module Prec = Prec
