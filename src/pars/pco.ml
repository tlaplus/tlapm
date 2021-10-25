(*
 * pars/pco.ml --- parsers (based on lazy lists)
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** Parsers implementation *)

module LL = LazyList

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

module Make (Tok : Intf.Tok) (Prec : Intf.Prec) = struct

  module Tok = Tok
  module Prec = Prec

  include Tok

  type 's pstate = {
    (* input *)
    mutable source : token LL.t ;

    (* last read token *)
    mutable lastpos : Loc.locus ;

    (* user state *)
    mutable ustate : 's ;
  }

  (* kind of failure *)
  type kind =
    | Unexpected of string
        (** encountered an unexpected token *)
    | Message of string
        (** failed with user-provided reason *)
    | Internal of string
        (** failed with internal reason *)

  (* severity of failure *)
  type severity =
    | Backtrack
        (** normal failure attempting inapplicable rule *)
    | Abort
        (** partially applied rule giving unambiguous failure *)

  (* result of parsing *)
  type 'a result =
    | Parsed of 'a
    | Failed of kind * severity * string option

  type ('s, 'a) reply = {
    res : 'a result ;
    loc : Loc.locus ;
  }

  let fuse aloc bloc =
    if aloc = Loc.unknown || aloc.Loc.start = aloc.Loc.stop then bloc
    else if bloc = Loc.unknown || bloc.Loc.start = bloc.Loc.stop then aloc
    else Loc.merge aloc bloc

  type ('s, 'a) prs = Prs of ('s pstate -> ('s, 'a) reply)
  (* type ('s, 'a) prs = (\* Prs of *\) 's pstate -> ('s, 'a) reply *)

  (* running a parser *)

  let exec (Prs ap) pst = ap pst

  let execute ap pst =
    let rep = exec ap pst in
      match rep.res with
        | Parsed a -> Some a
        | Failed (fk, _, msg) ->
            let err = Error.error pst.lastpos in
            let err = match fk with
              | Unexpected un -> Error.err_set_unexpected un err
              | Message msg -> Error.err_add_message msg err
              | Internal msg -> Error.err_add_internal msg err
            in
              Error.print_error ~verbose:true stderr err ;
              None

  let run ap ~init ~source =
    let pst = { source = source ;
                ustate = init ;
                lastpos = begin
                  match LL.expose source with
                    | LL.Nil -> failwith "No tokens in file"
                    | LL.Cons (t, _) ->
                        let loc = Tok.locus t in
                            { loc with Loc.start = loc.Loc.stop }
                end ;
              }
    in execute ap pst

  (* primitive parsers *)

  let return a loc = Prs begin
    fun pst ->
      (* pst.lastpos <- { loc with Loc.start = loc.Loc.stop } ; *)
      { res = Parsed a ;
        loc = loc }
  end

  let succeed a = Prs begin
    fun pst ->
      { res = Parsed a ;
        loc = pst.lastpos ;
      }
  end

  let fail msg = Prs begin
    fun pst ->
      { res = Failed (Message msg, Backtrack, None) ;
        loc = pst.lastpos }
  end

  let internal msg = Prs begin
    fun pst ->
      { res = Failed (Internal msg, Backtrack, None) ;
        loc = pst.lastpos }
  end

  let debug msg = Prs begin
    fun pst ->
      let err = Error.error pst.lastpos in
      let err = Error.err_add_message (Printf.sprintf "[debug] following token is %s"
                                         (match LL.expose pst.source with
                                            | LL.Nil -> "EOF"
                                            | LL.Cons (t, _) -> Tok.rep t)) err in
      let err = Error.err_add_message (Printf.sprintf "[debug] %s" msg) err in
        Error.print_error stderr err ;
        exec (succeed ()) pst
  end

  let report ?(verb=1) msg ap = Prs begin
    fun pst ->
      let yell what =
        let err = Error.error pst.lastpos in
        let err = Error.err_add_message (Printf.sprintf "[debug] %s" what) err in
          Error.print_error stderr err
      in
      if verb > 3 then
        yell (msg ^ " start") ;
      let rep = exec ap pst in
      if verb > 2 then
        yell (msg ^ " end") ;
      begin match rep.res with
        | Parsed _ ->
            if verb > 2 then
              yell (msg ^ " success")
        | Failed (_, Backtrack, _) ->
            if verb > 1 then
              yell (msg ^ " backtrack")
        | Failed (_, Abort, _) ->
            yell (msg ^ " ABORT")
      end ;
      rep
  end

  (* state *)

  let get = Prs begin
    fun pst -> exec (succeed pst.ustate) pst
  end

  let morph f = Prs begin
    fun pst ->
      pst.ustate <- f pst.ustate ;
      exec (succeed ()) pst
  end

  let put s = morph (fun _ -> s)

  let using s ap = Prs begin
    fun pst ->
      let oldst = pst.ustate in
        pst.ustate <- s ;
        let rep = exec ap pst in
          pst.ustate <- oldst ;
          rep
  end

  (* delay *)

  let use apf = Prs begin
    fun pst -> exec (Lazy.force apf) pst
  end

  let thunk apf = Prs begin
    fun pst -> exec (apf ()) pst
  end

  (* primitive combinators *)

  let ( >>+ ) ap bpf = Prs begin
    fun pst ->
      let arep = exec ap pst in
        match arep.res with
          | Parsed a ->
              let brep = exec (bpf a arep.loc) pst in
                brep
          | Failed (fk, sev, fn)->
              { arep with res = Failed (fk, sev, fn) }
  end

  let ( >>= ) ap bpf = ap >>+ (fun a _ -> bpf a)

  let ( <|> ) ap bp = Prs begin
    fun pst ->
      let arep = exec ap pst in
      match arep.res with
        | Failed (_, Backtrack, _) ->
            exec bp pst
        | _ -> arep
  end

  let ( <*> ) ap bp =
    ap >>+ fun a aloc ->
      bp >>+ fun b bloc ->
        return (a, b) (fuse aloc bloc)

  (* explanations *)

  let commit ap = Prs begin
    fun pst ->
      match exec ap pst with
        | { res = Failed (fk, sev, msg) } as rep ->
            (*
             * if sev = Backtrack then
             *   ignore (exec (debug "abort!") pst) ;
             *)
            { rep with res = Failed (fk, Abort, msg) }
        | rep -> rep
  end

  let ( <**> ) ap bp =
    ap <*> commit bp

  let explain name ap = Prs begin
    fun pst ->
      let arep = exec ap pst in
        match arep.res with
          | Failed (fk, sev, None) ->
              { arep with res = Failed (fk, sev, Some name) }
          | _ ->
              arep
  end

  let ( <$> ) ap f =
    ap >>+ fun a loc -> return (f a) loc

  let ( >>> ) ap bp = (ap <*> bp) <$> snd

  let ( >*> ) ap bp = (ap <*> commit bp) <$> snd

  let ( <<< ) ap bp = (ap <*> bp) <$> fst

  let ( <!> ) ap x = ap >>> succeed x

  let ( <::> ) ap lp =
    ap <*> lp <$> (fun (a, l) -> a :: l)

  let ( <@> ) alp blp =
    alp <*> blp <$> (fun (al, bl) -> al @ bl)

  let withloc ap = Prs begin
    fun pst ->
      let rep = exec ap pst in
        { rep with res =
            match rep.res with
              | Parsed a ->
                  Parsed (a, rep.loc)
              | Failed (fk, sev, msg) ->
                  Failed (fk, sev, msg) }
  end

  let save pst =
    (pst.source, pst.lastpos, pst.ustate)

  let restore (s, l, u) pst =
    pst.source <- s;
    pst.lastpos <- l;
    pst.ustate <- u

  let lookahead ap = Prs begin
    fun pst ->
      let locus = save pst in
      let rep = exec ap pst in
        restore locus pst ;
        rep
  end

  let enabled ap =
    lookahead ap >>= fun _ -> succeed ()

  let disabled ap =
    (lookahead ap >>= (fun _ -> fail "not disabled")) <|> succeed ()

  let attempt ap = Prs begin
    fun pst ->
      let memo = save pst in
      let arep = exec ap pst in
        match arep.res with
          | Failed _ ->
              restore memo pst ;
              arep
          | _ -> arep
  end

  let optional ap = (attempt ap <$> fun n -> Some n) <|> succeed None

  let (<?>) ap g =
    attempt begin
      ap >>+ fun a loc ->
        if g a then return a loc else internal "<?>"
    end

  let (<$?>) ap g =
    attempt begin
      ap >>+ fun a loc ->
        match g a with
          | Some b -> return b loc
          | None -> internal "<?>"
    end

  (* alternation *)

  let rec choice = function
    | [] -> invalid_arg "null alternative"
    | [ap] -> ap
    | ap :: aps ->
        ap <|> choice aps

  let rec alt = function
    | [] -> invalid_arg "null alternative"
    | [ap] -> ap
    | ap :: aps ->
        attempt ap <|> alt aps

  (* sequence parsers *)

  let rec seq = function
    | [] -> succeed []
    | ap :: aps ->
        ap <::> seq aps

  let ix f =
    let rec run n =
      (f n <::> run (n + 1)) <|> succeed []
    in
      run 0

  (* Kleene star *)

  let star ap =
    let rec aps = lazy begin
      alt [
        ap <::> use aps ;
        ap <$> (fun x -> [x]) ;
        succeed [] ;
      ]
    end in
    (* let rec aps = lazy (attempt (ap <::> use aps) <|> succeed []) in *)
      use aps

  (*
   * let star ap =
   *   fix (fun st -> attempt (ap <::> st) <|> succeed [])
   *)

  let star1 ap = ap <::> star ap

  let sep1 sp ap =
    ap <::> star (sp >>> ap)

  let sep sp ap =
    sep1 sp ap <|> succeed []

  (* token parsers *)

  (*
   * let peek = Prs begin
   *   fun pst ->
   *     match LL.expose pst.source with
   *       | LL.Cons (t, src) ->
   *           let tloc = Tok.locus t in
   *             pst.lastpos <- { tloc with Loc.start = tloc.Loc.stop } ;
   *             { res = Parsed (Some t) ;
   *               loc = pst.lastpos }
   *       | LL.Nil ->
   *           { res = Parsed None ;
   *             loc = pst.lastpos }
   * end
   *)

  let scan check = Prs begin
    fun pst ->
      match LL.expose pst.source with
        | LL.Cons (t, src) -> begin
            let tloc = Tok.locus t in
              match check t with
                | Some a ->
                    pst.source <- src ;
                    pst.lastpos <- { tloc with Loc.start = tloc.Loc.stop } ;
                    { res = Parsed a ;
                      loc = tloc }
                | None ->
                    { res = Failed (Unexpected (Tok.rep t), Backtrack, None) ;
                      loc = tloc }

          end
        | LL.Nil ->
            { res = Failed (Unexpected "EOF", Backtrack, None) ;
              loc = pst.lastpos }
  end

  let satisfy tf = scan (fun t -> if tf t then Some t else None)

  (* has to be written this way because of the value restriction *)
  let any = Prs (fun pst -> exec (satisfy (fun _ -> true)) pst)

  let literal c = satisfy (fun t -> c = t) <!> ()

  let string cs =
    seq (List.map literal cs) <!> ()

  (* lifts *)

  let lift1 f ap =
    ap >>= fun a ->
      succeed (f a)

  let lift2 f ap bp =
    ap >>= fun a ->
      bp >>= fun b ->
        succeed (f a b)

  let lift3 f ap bp cp =
    ap >>= fun a ->
      bp >>= fun b ->
        cp >>= fun c ->
          succeed (f a b c)

  let lift4 f ap bp cp dp =
    ap >>= fun a ->
      bp >>= fun b ->
        cp >>= fun c ->
          dp >>= fun d ->
            succeed (f a b c d)

  let lift5 f ap bp cp dp ep =
    ap >>= fun a ->
      bp >>= fun b ->
        cp >>= fun c ->
          dp >>= fun d ->
            ep >>= fun e ->
              succeed (f a b c d e)

  include Prec

  type assoc = Left | Right | Non

  type 'a item =
    | Atm of 'a
    | Opr of prec * 'a opr

  and 'a opr =
    | Prefix of (Loc.locus -> 'a -> 'a)
    | Postfix of (Loc.locus -> 'a -> 'a)
    | Infix of assoc * (Loc.locus -> 'a -> 'a -> 'a)

  let resolve (item_prs : bool -> ('s, 'a item list) prs) : ('s, 'a) prs =
    let exception Reduce_one_exn in
    let rec next stack startp =
      attempt (item_prs startp >>+ decide_fork stack) <|> use (lazy (finish stack))

    and decide_fork stack items loc = match items with
      | [item] -> decide stack (item, loc)
      | _ -> choice (List.map (fun item -> decide stack (item, loc)) items)

    and decide stack (item, loc) = match item with
      | Atm _ | Opr (_, Prefix _) -> begin
          match stack with
            | (Atm _, _) :: _ ->
                fail "missing operator"
            | _ ->
                commit begin
                  next ((item, loc) :: stack) begin
                    match item with
                      | Atm _ -> false    (* cannot start exp following atom *)
                      | _ -> true         (* can start exp following prefix  *)
                  end
                end
        end
      | Opr (oprec, Infix (oass, _)) -> begin
          let rec normalize stack = match stack with
            | _ :: (Opr (pprec, _), _) :: _
                when below oprec pprec ->
                normalize (reduce_one stack)
            | _ :: (Opr (pprec, Infix (Left, _)), _) :: _
                when oass = Left && not (below pprec oprec) ->
                reduce_one stack
            | _ -> stack
          in
          let stack = normalize stack in
            match stack with
              | (Atm _, _) :: _ ->
                  commit (next ((item, loc) :: stack) true)
              | _ :: _ ->
                  fail "missing operator"
              | [] ->
                  fail "insufficient arguments"
        end
      | Opr (oprec, Postfix _) -> begin
          let rec normalize stack = match stack with
            | _ :: (Opr (pprec, _), _) :: _ when below oprec pprec ->
                normalize (reduce_one stack)
            | _ -> stack
          in
          let stack = normalize stack in
            match stack with
              | (Atm _, _) :: _ ->
                  commit (next (reduce_one ((item, loc) :: stack)) false)
              | _ :: _ ->
                  fail "missing operator"
              | [] ->
                  fail "insufficient arguments"
        end

    and reduce_one = function
      | (Opr (_, Postfix px), oloc)
        :: (Atm a, aloc)
        :: stack ->
          (Atm (px oloc a), fuse aloc oloc)
          :: stack
      | (Atm b, bloc)
        :: (Opr (_, Infix (_, ix)), oloc)
        :: (Atm a, aloc)
        :: stack ->
          (Atm (ix oloc a b), fuse aloc (fuse oloc bloc))
          :: stack
      | (Atm a, aloc)
        :: (Opr (_, Prefix px), oloc)
        :: stack ->
          (Atm (px oloc a), fuse oloc aloc)
          :: stack
      | _ ->
          raise Reduce_one_exn

    and finish stack = match stack with
        | [(Atm a, loc)] -> return a loc
        | [] ->
            lookahead any >>= fun t ->
              fail ("required expressions(s) missing before '" ^ Tok.rep t ^ "'")
        | _ -> begin
            try finish (reduce_one stack) with
              | Reduce_one_exn -> fail "incomplete expression"
          end

    in next [] true

end
