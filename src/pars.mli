(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

module Error : sig
  type error                          (** The abstract type of errors *)
  type t = error                      (** convenience *)
  val error : Loc.locus -> error
  val err_combine : error -> error -> error
  val err_add_message : string -> error -> error
  val err_add_internal : string -> error -> error
  val err_add_expecting : string -> error -> error
  val err_set_unexpected : string -> error -> error
  val print_error : ?verbose:bool -> Pervasives.out_channel -> error -> unit
end;;

module Intf : sig
  module type Tok = sig
    type token
    val bof : Loc.locus -> token
    val rep : token -> string
    val locus : token -> Loc.locus
    val eq : token -> token -> bool
    val pp_print_token : Format.formatter -> token -> unit
  end

  (** Precedence *)
  module type Prec = sig
    type prec
    val below : prec -> prec -> bool
    val conflict : prec -> prec -> bool
  end
end;;

module LazyList : sig
  type +'a llist
  type 'a t = 'a llist
  type 'a front = Nil | Cons of 'a * 'a t
  val expose : 'a llist -> 'a front
  val exact : 'a * 'a llist -> 'a llist
  val delay : (unit -> 'a * 'a llist) -> 'a llist
  val empty : 'a llist
  val cons : 'a -> 'a llist -> 'a llist
  val length : 'a llist -> int
  val null : 'a llist -> bool
  val hd : 'a llist -> 'a
  val tl : 'a llist -> 'a llist
  val take : int -> 'a llist -> 'a llist
  val drop : int -> 'a llist -> 'a llist
  val (@@) : 'a llist -> 'a llist -> 'a llist
  val concat : 'a llist list -> 'a llist
  val rev : 'a llist -> 'a llist
  val map : ('a -> 'b) -> 'a llist -> 'b llist
  val filter : ('a -> bool) -> 'a llist -> 'a llist
  val filter_map : ('a -> 'b option) -> 'a llist -> 'b llist
  val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b llist -> 'a
  val fold_right : ('a -> 'b -> 'b) -> 'a llist -> 'b -> 'b
  val unfold : 'a -> ('a -> ('b * 'a) option) -> 'b llist
  val make : (unit -> 'a option) -> 'a llist
end;;

module Pco : sig
  module type Make_sig = sig
    module Tok : Intf.Tok
    module Prec : Intf.Prec
    type ('s, 'a) prs
    val run :
      ('s, 'a) prs ->
      init:'s ->
      source:Tok.token LazyList.t ->
      'a option
    val return : 'a -> Loc.locus -> ('s, 'a) prs
    val succeed : 'a -> ('s, 'a) prs
    val fail : string -> ('s, 'a) prs
    val debug : string -> ('s, unit) prs
    val report : ?verb:int -> string -> ('s, 'a) prs -> ('s, 'a) prs
    val explain : string -> ('s, 'a) prs -> ('s, 'a) prs
    val withloc : ('s, 'a) prs -> ('s, 'a * Loc.locus) prs
    val get : ('s, 's) prs
    val put : 's -> ('s, unit) prs
    val morph : ('s -> 's) -> ('s, unit) prs
    val using : 's -> ('s, 'a) prs -> ('s, 'a) prs
    val use : ('s, 'a) prs Lazy.t -> ('s, 'a) prs
    val thunk : (unit -> ('s, 'a) prs) -> ('s, 'a) prs
    val ( >>+ ) :
      ('s, 'a) prs -> ('a -> Loc.locus -> ('s, 'b) prs) -> ('s, 'b) prs
    val ( <|> ) : ('s, 'a) prs -> ('s, 'a) prs -> ('s, 'a) prs
    val ( <*>  ) : ('s, 'a) prs -> ('s, 'b) prs -> ('s, 'a * 'b) prs
    val commit : ('s, 'a) prs -> ('s, 'a) prs
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
    val lookahead : ('s, 'a) prs -> ('s, 'a) prs
    val enabled : ('s, 'a) prs -> ('s, unit) prs
    val disabled : ('s, 'a) prs -> ('s, unit) prs
    val attempt : ('s, 'a) prs -> ('s, 'a) prs
    val optional : ('s, 'a) prs -> ('s, 'a option) prs
    val choice : ('s, 'a) prs list -> ('s, 'a) prs
    val alt : ('s, 'a) prs list -> ('s, 'a) prs
    val seq : ('s, 'a) prs list -> ('s, 'a list) prs
    val ix : (int -> ('s, 'a) prs) -> ('s, 'a list) prs
    val star : ('s, 'a) prs -> ('s, 'a list) prs
    val star1 : ('s, 'a) prs -> ('s, 'a list) prs
    val sep : ('s, 'sep) prs -> ('s, 'a) prs -> ('s, 'a list) prs
    val sep1 : ('s, 'sep) prs -> ('s, 'a) prs -> ('s, 'a list) prs
    val scan : (Tok.token -> 'a option) -> ('s, 'a) prs
    val satisfy : (Tok.token -> bool) -> ('s, Tok.token) prs
    val any : ('s, Tok.token) prs
    val literal : Tok.token -> ('s, unit) prs
    val string : Tok.token list -> ('s, unit) prs
    type assoc = Left | Right | Non
    type 'a item =
      | Atm of 'a
      | Opr of Prec.prec * 'a opr
    and 'a opr =
      | Prefix of (Loc.locus -> 'a -> 'a)
      | Postfix of (Loc.locus -> 'a -> 'a)
      | Infix of assoc * (Loc.locus -> 'a -> 'a -> 'a)
    val resolve : (bool -> ('s, 'a item list) prs) -> ('s, 'a) prs
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
      ('s, 'a) prs ->
      ('s, 'b) prs ->
      ('s, 'c) prs ->
      ('s, 'd) prs ->
        ('s, 'e) prs
    val lift5 :
      ('a -> 'b -> 'c -> 'd -> 'e -> 'f) ->
      ('s, 'a) prs ->
      ('s, 'b) prs ->
      ('s, 'c) prs ->
      ('s, 'd) prs ->
      ('s, 'e) prs ->
        ('s, 'f) prs
  end

  module Make (Tok : Intf.Tok) (Prec : Intf.Prec) :
    Make_sig with module Tok = Tok and module Prec = Prec
  ;;
end;;
