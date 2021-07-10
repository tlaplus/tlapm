(* Rewriting rules.

Author: Hern\'an Vanzetto <hernan.vanzetto@inria.fr>

Copyright (C) 2011-2012  INRIA and Microsoft Corporation
*)
open Ext
open Property

open Expr.T
open Expr.Subst
open Expr.Visit

open Printf
open List

module B = Builtin
module Dq = Deque
module Fu = Fmtutil.Minimal (Tla_parser.Prec)
module Smt = Smtcommons
module T = Typ_t

(****************************************************************************)

(** Note that Internal B.Range is a set only when its arguments are integers. *)
let is_set e =
  match e.core with
  | Apply ({core = Internal B.Cup | Internal B.Cap | Internal B.Setminus | Internal B.SUBSET | Internal B.UNION}, _)
  | SetOf _ | SetSt _ | SetEnum _ | Rect _ | Product _
  | Arrow _
  | Internal B.Nat | Internal B.Seq
      -> true
  | _ -> false

let is_Int scx e = T.is_int (snd scx) e

let ( <<< ) = T.( <<< )

let rw_arith = new Rewrite_arith.rw

(****************************************************************************)

let is_true  e = Expr.Eq.expr e (Internal B.TRUE %% [])
let is_false e = Expr.Eq.expr e (Internal B.FALSE %% [])

let get_tybase scx x =
  let tybase = function Some (T.Set t) -> Some t | _ -> None in
  let ty = T.get_type (snd scx) x in
(* Util.eprintf "  get_tybase  %a = %a" (Typ_e.pp_print_expr (snd scx, Ctx.dot)) x Typ_e.ppt (Typ_e.empty, Option.default T.Top ty); *)
  tybase ty

(****************************************************************************)

(** When [e] is a function with domain [1..n] or [{1, ..., n}],
    it returns [e] decomposed in the bound variable, the domain, etc. *)
let extract_domain_from_function e =
  match e.core with
  | Fcn ([h,_,Domain ({core = Apply ({core = Internal B.Range},
      [{core = Num ("1","")} ; n])} as dom)], ex) ->
    (** e == [h \in 1..n |-> ex] *)
    Some (h, n, dom, ex)
  | Fcn ([h,_,Domain ({core = SetEnum es} as dom)], ex) ->
        (** e == [h \in {1, ..., n} |-> ex] *)
    let n' = length es in
    let n = Num (string_of_int n', "") @@ e in
    if es = Rewrite_trivial.range2set 1 n' then Some (h, n, dom, ex) else None
  | _ ->
    None

let is_function_with_explicit_domain e = extract_domain_from_function e <> None

class rw = object (self : 'self)
  inherit [unit] Expr.Visit.map as super
  method hyp scx h =
    match h.core with
    | Defn (_, _, Hidden, _)    (** ignore these cases *)
    | Fact (_, Hidden, _) ->
      (adj scx h, h)
    | _ ->
      super#hyp scx h
  method expr scx e =
(* Util.eprintf "rw: %a" (Expr.Fmt.pp_print_expr (snd scx, Ctx.dot)) e ; *)
    let mk x = { e with core = x } in
    let mn x = noprops x in
    let build ex = match ex.core with a -> a |> mk in                           (** mantains e's original properties, especially [Boolify.boolify_prop] -- Not used *)
    let apply1 op ex    = Apply (Internal op |> mk, [ex]) |> mk in
    let apply2 op e1 e2 = Apply (Internal op |> mk, [e1 ; e2]) |> mk  in
    let opq id = function [] -> Opaque id |> mk | es -> Apply (Opaque id |> mn, es) |> mk in
    let fcnapp f x = FcnApp (f, [x]) |> mk in
    let fcnapp_u scx f x = opq Smt.fcnapp [f ; x] in
    let dot r h = Dot (r, h) |> mk in
    let ix1 = Ix 1 |> mn in
    let sh1 e = app_expr (shift 1) e in
    let ( <~ ) ex y = app_expr (scons y (shift 0)) ex in                        (** substitutes [Ix 1] by [y] in [ex] *)
    let quant q h dom typ ex =
      let h = match typ with Some t -> h <<< t | None -> h in
      let dom = match dom with
        | Some d ->
          (* let t = TLAtype.base (typpbot d) in *)
          (* types#update ((* quant_id *) h.core) t ; *)
          (* let h = assign h boundvar () in *)
          [h, Unknown, Domain d]
        | None ->
          [h, Unknown, No_domain]
      in
      Quant (q, dom, ex) |> mk in
    let forall ?id:(h=Smt.fresh_name () |> mk) ?typ:(t=None) ?dom ex = quant Forall h dom t ex in
    let exists ?id:(h=Smt.fresh_name () |> mk) ?typ:(t=None) ?dom ex = quant Exists h dom t ex in
    let lAnd es = List (And, es) |> mk in
    let lAndx = function [e] -> e | es -> List (And, es) |> mk in
    let lOr es = List (Or, es) |> mk in
    let domain ex   = Apply (Internal B.DOMAIN |> mk, [ex]) |> mk in
    let mem x y     = apply2 B.Mem x y in
    let implies x y = apply2 B.Implies x y in
    let eq x y      = apply2 B.Eq x y in
    let equiv x y   = apply2 B.Equiv x y in
    let conj x y    = apply2 B.Conj x y in
    let disj x y    = apply2 B.Disj x y in
    let neg x       = apply1 B.Neg x in
    let len x       = apply1 B.Len x in
    let range x y   = apply2 B.Range x y in
    let plus x y    = apply2 B.Plus x y in
    let minus x y   = apply2 B.Minus x y in
    let lt x y      = apply2 B.Lt x y in
    let setminus x y = apply2 B.Setminus x y in
    let boolify e = if T.is_hard_bool e then e else opq "boolify" [e] in
    let isAFcn x  =
      (* types#update "tla__isAFcn" (Fcn(Fcn(Bot,Bot),Bool)) ; *)
      (* noprops (Apply (noprops (Opaque "tla__isAFcn"), [x])) *)
      opq "tla__isAFcn" [x] in
    let str s = String s |> mn in
    let ifte c t f = If (c,t,f) |> mk in
    let ifte_bool c t f =
      if !Smt.mode = Smt.Spass || !Smt.mode = Smt.Fof
      then conj (implies c t) (implies (neg c) f)
      else ifte c t f
    in
    (* let ifte_eq p c t f = if mem_simplefacts cx c then p t else forall (implies (ifte (sh1 c) (eq ix1 (sh1 t)) (eq ix1 (sh1 f))) (sh1 (p (Ix 0 |> mk)))) in *)
    let tla_true  = Internal B.TRUE  |> mk in
    let tla_false = Internal B.FALSE |> mk in
    let zero = Num ("0","") |> mk in
    let one = Num ("1","") |> mk in
    let ints = Internal B.Int |> mk in
    let nats = Internal B.Nat |> mk in
    let leq x y = apply2 B.Lteq x y in
    let mk_num n = Num (string_of_int n,"") |> mk in
    let empty_tuple = Tuple [] |> mk in
    let empty_set = SetEnum [] |> mk in
    (* let str_is_int x = try int_of_string x = int_of_string x with _ -> false in *)
    (* let str_is_nat x = try int_of_string x >= 0 with _ -> false in *)
    (* let string_of_float' x = Str.replace_first (Str.regexp "^\\(.*\\)\\.$") "\\1" (string_of_float x) in *)
    let e = Rewrite_trivial.rw e in
    (* let e = if !Smt.mode = Fof then e else rw_arith#expr scx e in *)
    let e = rw_arith#expr scx e in
    let unspec scx e = Opaque ("newvar__" ^ (Smt.fresh_id ())) @@ e in    (** FIX *)
    let dummy = (Fresh ("dummy" %% [], Shape_expr, Constant, Unbounded) %% []) in
    let rw_mem x y =
      match x.core, y.core with
      | _, If (c,t,f) when Smt.is_term x || is_set x ->
        ifte c (mem x t) (mem x f) |> self#expr scx
      | If (c,t,f), _ when Smt.is_term y || is_set y ->
        ifte c (mem t y) (mem f y) |> self#expr scx
      (* | _, If (c,t,f) when is_term x || is_set x -> ifte_bool c (mem x t) (mem x f) |> self#expr scx
      | If (c,t,f), _ when is_term y || is_set y -> ifte_bool c (mem t y) (mem f y) |> self#expr scx *)
      (* | _, If (c,t,f) -> self#expr scx (ifte_eq (mem x) c t f)
      | If (c,t,f), _ -> self#expr scx (ifte_eq (fun x -> mem x y) c t f) *)

      | Apply ({core = Opaque "bool2u"}, [e]), Internal B.BOOLEAN when T.is_hard_bool e ->
        tla_true
      | _, Internal B.BOOLEAN when T.is_hard_bool x ->
        tla_true
      (* | _, Internal B.BOOLEAN when T.is_bool (snd scx) x -> tla_true *)

      | _, Apply ({core = Internal op2}, [ex]) ->
        let ex = self#expr scx ex in
        begin match op2, ex.core with
        | B.SUBSET, _ ->
          apply2 B.Subseteq x ex |> self#expr scx
        | B.UNION, SetEnum es ->
          lOr (map (mem x) es) |> self#expr scx
        | B.UNION, SetOf (ex, ([v,_,Domain s])) ->
          exists ~dom:s ~typ:(get_tybase scx s) (mem (sh1 x) ex) |> self#expr scx
        | B.UNION, SetSt (v, s, p) ->
          exists ~dom:s ~typ:(get_tybase scx s) (lAnd [p ; mem (sh1 x) ix1]) |> self#expr scx
        | B.UNION, _ ->
          exists ~dom:ex ~typ:(get_tybase scx ex) (mem (sh1 x) ix1) |> self#expr scx

        (** x \in Seq(ex) --> ... *)
        | B.Seq, _ ->
          begin match x.core with
            (** <<e1, ..., en>> \in Seq(ex) --> e1 \in ex /\ ... /\ en \in ex *)
            | Tuple es ->
              let es = map (self#expr scx) es in
              lAnd (map (fun e -> mem e ex) es) |> self#expr scx

            (** [h \in 1..n |- ex1] \in Seq(ex) --> \A h \in 1..n:  ex1 \in ex *)
            | _ when is_function_with_explicit_domain x ->
              let h,n,dom,ex1 = Option.get (extract_domain_from_function x) in
              let ex1 = self#expr scx ex1 in
              let dom = self#expr scx dom in
              if is_Int scx n
              then forall ~id:h ~dom:dom ~typ:(get_tybase scx dom) (mem ex1 (sh1 ex)) |> self#expr scx
              else mem x y

            (* | Fcn ([h,_,Domain ({core = Apply ({core = Internal B.Range}, [{core = Num ("1","")} ; n])} as dom)], ex1) when is_Int scx n ->
                self#expr scx (forall ~id:h ~dom:dom (mem ex1 (sh1 ex))) *)
                (** FIX: mem n nats is a condition *)
                (* self#expr scx (lAnd [mem n nats ; forall ~id:h ~dom:dom (mem ex1 (sh1 ex))]) *)

            (** Tail(t) \in Seq(ex)  -->  t # <<>> /\ t \in Seq(ex) *)
            | Apply ({core = Internal B.Tail}, [t]) ->
              lAnd [neg (eq t empty_tuple) ; mem t y] |> self#expr scx

            (** Append(t,e) \in Seq(ex)  -->  t \in Seq(ex) /\ e \in ex *)
            | Apply ({core = Internal B.Append}, [t ; e]) ->
              lAnd [mem t y ; mem e ex] |> self#expr scx

            (** Cat(r,t) \in Seq(ex)  -->  r \in Seq(ex) /\ t \in Seq(ex) *)
            | Apply ({core = Internal B.Cat}, [r ; t]) ->
              lAnd [mem r y ; mem t y] |> self#expr scx

            (** SubSeq(s,m,n) \in Seq(ex) -->
                /\ s \in Seq(ex)
                /\ m \in Int
                /\ n \in Int
            | Apply ({core = Internal B.SubSeq}, [s ; m ; n]) ->
                lAnd [mem s y ; mem m ints ; mem n ints] |> self#expr scx
            *)

            (** SubSeq(s,m,n) \in Seq(ex)  -->
                /\ m \in Int
                /\ n \in Int
                /\ \A i \in m .. n:  s[m] \in ex
            *)
            | Apply ({core = Internal B.SubSeq}, [s ; m ; n]) ->
              lAnd [
                mem m ints ; mem n ints ;
                forall ~dom:(range m n) ~typ:(Some T.Int)
                  (mem (fcnapp (sh1 s) ix1) (sh1 ex))
              ] |> self#expr scx

            (** [s EXCEPT ![a] = b] \in Seq(ex)  -->
                /\ s \in Seq(ex)
                /\ a \in 1..Len(s)
                /\ b \in ex
            *)
            | Except (s, [([Except_apply a], b)]) ->
              lAnd [mem s y ; mem a (range one (len s)) ; mem b ex] |> self#expr scx

            (* | _ ->
                self#expr scx (mem x (Apply (Internal B.UNION |> mk, [SetOf (Arrow (range one ix1, sh1 s) |> mk, ([fresh_name () |> mk,Unknown,Domain nats])) |> mk]) |> mk)) *)
            (* | _ ->
                let dom = range one ix1 in
                self#expr scx (lAnd [isAFcn x ; exists ~dom:nats
                            (lAnd [mem ix1 nats ;
                                   eq (domain (sh1 x)) dom ;
                                   (* eq ix1 (len (sh1 x)) ; *)
                                   forall ~dom:dom (implies (mem ix1 (sh1 dom)) (mem (fcnapp (sh1 (sh1 x)) ix1) (sh1 (sh1 s))))
                                   ])]) *)
            | _ ->
              mem x (apply1 op2 ex)
          end
        | _ ->
          mem x (apply1 op2 ex)
        end
      | _, Apply ({core = Internal op2}, [e1 ; e2]) ->
        let e1 = self#expr scx e1 in
        let e2 = self#expr scx e2 in
        begin match op2 with
          | B.Cup ->
            disj (mem x e1) (mem x e2) |> self#expr scx
          | B.Cap ->
            conj (mem x e1) (mem x e2) |> self#expr scx
          | B.Setminus ->
            conj (mem x e1) (neg (mem x e2)) |> self#expr scx
          | B.Range ->
            lAnd [mem x (Internal B.Int |> mk) ; leq e1 x ; leq x e2] |> self#expr scx
          | _ ->
            mem x (apply2 op2 e1 e2)
        end
      | _, SetEnum [] ->
        tla_false
      | _, SetEnum es ->
        lOr (map (eq x) es) |> self#expr scx
      | _, SetOf (ex, bs) ->
        Quant (Exists, bs, eq (app_expr (shift (length bs)) x) ex) |> mk |> self#expr scx
      | _, SetSt (_, dom, p) ->
        conj (mem x dom) (p <~ x) |> self#expr scx
      | _, Product es ->
        lAnd
          (isAFcn x ::
           eq (domain x) (range one (mk_num (length es))) ::
           (mapi (fun i ex -> mem (fcnapp_u scx x (mk_num (i+1))) ex) es))
        |> self#expr scx     (** CHECK fcnapp_u *)

      (* | Apply ({core = Internal B.Len}, [_]), Internal B.Nat -> tla_true *)         (** this is a BUG *)

      | Except (f, [([Except_apply a], b)]), Arrow (s, t) ->
        let scx' = adj scx dummy in
        let es = [
          isAFcn f ;
          eq (domain f) s ;
          mem a s ;
          mem b t ;
          forall ~dom:(setminus s (SetEnum [a] |> mk))
                 ~typ:(get_tybase scx s)
                 (mem (fcnapp_u scx' (sh1 f) ix1) (sh1 t))
        ] in
        let es = map (self#expr scx) es in
        lAnd es |> self#expr scx

      | Fcn ([_,_,Domain s'], ex), Arrow (s, t) ->
        let es = [
          eq s' s ;
          forall ~dom:s ~typ:(get_tybase scx s) (mem ex (sh1 t))
        ] in
        let es = map (self#expr scx) es in
        lAnd es |> self#expr scx

      | _, Arrow (s, t) ->
        let scx' = adj scx dummy in
        let es = [
          isAFcn x ;
          (* forall (equiv (mem ix1 (domain (sh1 x))) (mem ix1 (sh1 s))) ; *)
          eq (domain x) s ;
          (* forall ~dom:(domain x) (mem (fcnapp (sh1 x) ix1) (sh1 t)) *)
          forall ~dom:s ~typ:(get_tybase scx s) (mem (fcnapp_u scx' (sh1 x) ix1) (sh1 t))
          (* forall ~dom:s (implies (mem ix1 (domain (sh1 x))) (mem (fcnapp (sh1 x) ix1) (sh1 t)))      *)
          (* forall ~dom:s (implies (disj (mem ix1 (domain (sh1 x))) (mem ix1 (sh1 s))) (mem (fcnapp (sh1 x) ix1) (sh1 t)))      *)
        ] in
        let es = map (self#expr scx) es in
        lAnd es |> self#expr scx

      (* | Apply ({core = Internal B.Plus}, [a ; b]), (Internal B.Int | Internal B.Nat) ->
          lAnd [mem a y ; mem b y] |> self#expr scx
      | Apply ({core = Internal (B.Minus | B.Times | B.Exp) }, [a ; b]), Internal B.Int ->
          lAnd [mem a y ; mem b y] |> self#expr scx *)

      (** x::Int \in Int  --> TRUE *)
      | _, Internal B.Int when !Smt.mode != Smt.Fof && !Smt.mode != Smt.Spass && T.is_int (snd scx) x ->
        tla_true

      (** x \in Nat  -->  x \in Int /\ 0 <= x *)
      | _, Internal B.Nat ->
        conj (mem x (Internal B.Int |> mk))
             (leq (Num ("0","") |> mk) x)
        |> self#expr scx

      | Record rx, Rect rs when length rx = length rs ->
        let rx = Smt.rec_sort rx in
        let rs = Smt.rec_sort rs in
        let hs,_ = split rx in
        let fs,_ = split rs in
        let cdom = eq (SetEnum (map str hs) |> mk) (SetEnum (map str fs) |> mk) in
        lAnd (cdom ::
          (* (map (fun f -> mem (str f) (domain x)) fs) @ *)
              (map2 (fun (h,ex) (f,s) -> if h = f then mem ex s else tla_false) rx rs))
        |> self#expr scx

      | _, Rect rs ->
        let fs,_ = split rs in
        let cdom = eq (domain x) (SetEnum (map str fs) |> mk) in
        lAnd (isAFcn x ::
              cdom ::
              (map (fun (h,ex) -> mem (fcnapp_u scx x (str h)) ex) rs))
        |> self#expr scx

      | _ ->
        mem x y
    in
    let rw_eq x y =
      match x.core, y.core with
      | _, Rect rs ->
        let scx' = adj scx dummy in
        let fs,_ = split rs in
        forall
          (equiv
            (mem ix1 (sh1 x))
            (lAnd begin
              isAFcn x ::
              (eq (domain (sh1 x)) (SetEnum (map str fs) |> mk)) ::
              (* (map (fun f -> mem (str f) (domain (sh1 x))) fs) @ *)
              (map (fun (h,e) -> mem (fcnapp_u scx' ix1 (str h)) (sh1 e)) rs)
            end
            ))                                                                  (*** Unbounded quantifier! *)
        |> self#expr scx
      | Rect _, _ ->
        eq y x |> self#expr scx

      (** DOMAIN f = {} --> f = <<>> *)
      | Apply ({core = Internal B.DOMAIN}, [f]), SetEnum []
      | SetEnum [], Apply ({core = Internal B.DOMAIN}, [f]) ->
        eq f empty_tuple |> self#expr scx

      (* | _, Apply ({core = Internal B.DOMAIN}, [{core = Apply ({core = Internal B.Tail}, [s])}]) ->
          self#expr scx (implies (neg (eq s empty_tuple)) (eq x (range one (minus (len s) one) )))
      | Apply ({core = Internal B.DOMAIN}, [{core = Apply ({core = Internal B.Tail}, [s])}]), _ ->
          self#expr scx (Apply (o, [y ; x]) |> mk) *)

      (** These rules keep the domain definitions *)
      | Apply ({core = Internal B.DOMAIN}, _), _
      | _, Apply ({core = Internal B.DOMAIN}, _) ->
        eq x y

      (** [s -> t] = {} --> s # {} /\ t = {} *)
      | SetEnum [], Arrow (s,t)
      | Arrow (s,t), SetEnum [] ->
        lAnd [
          apply2 B.Neq s empty_set ;
          eq t empty_set
        ] |> self#expr scx
(*
      (** (a..b) = {} -->
          /\ a \in Int
          /\ b \in Int
          /\ b < a
      *)
      | SetEnum [], Apply ({core = Internal B.Range}, [a;b])
      | Apply ({core = Internal B.Range}, [a;b]), SetEnum [] ->
        lAnd [mem a ints ; mem b ints ; lt b a] |> self#expr scx
*)
      (** x = {} --> \A z:  ~ (z \in x) *)
      | _, SetEnum [] ->
        forall ~typ:(get_tybase scx x) (neg (mem ix1 (sh1 x)))                  (*** Unbounded quantifier! *)
        |> self#expr scx
      | SetEnum [], _ ->
        eq y x |> self#expr scx

      | _, _ when is_set x || is_set y ->
        forall (equiv (mem ix1 (sh1 x)) (mem ix1 (sh1 y)))                      (*** Unbounded quantifier! *)
        |> self#expr scx

      | Fcn ([_,_,Domain s], e1), Fcn ([_,_,Domain t], e2) ->
        lAnd [ eq s t ; forall ~dom:s ~typ:(get_tybase scx s) (eq e1 e2) ]
        |> self#expr scx

      | _, Fcn ([_,_,Domain dom] as bs, ex) when Smt.is_term x ->               (** TODO: bs with more than one element *)
        let scx' = adj scx dummy in
        let isb = T.is_hard_bool ex in
        (* let isb = T.is_bool (snd scx) ex in *)
        let conn x y = if isb then equiv (boolify x) y else eq x y in           (** PROVE *)
        lAnd [
          isAFcn x ;
          eq (domain x) dom ;
          Quant (Forall, bs, conn (fcnapp_u scx' (sh1 x) ix1) ex) |> mk
        ] |> self#expr scx

      | Fcn _, _ when Smt.is_term y ->
        eq y x |> self#expr scx

      (** [_ \in s |-> _] = <<>> --> s = {} *)
      | Fcn ([_,_,Domain s], _), Tuple [] ->
        eq s empty_set |> self#expr scx

      (** Cat(s, t) = <<>> -->
          /\ s = <<>>
          /\ t = <<>>
      *)
      | Apply ({core = Internal B.Cat}, [s ; t]), Tuple [] ->
        lAnd [eq s y ; eq t y] |> self#expr scx

      (** SubSeq(s,m,n) = <<>> -->
          \/ s = <<>>
          \/ 1 .. 1 + n - m = {}
      *)
      | Apply ({core = Internal B.SubSeq}, [s ; m ; n]), Tuple [] ->
        lOr [ eq s empty_tuple ;
              eq (range one (minus (plus one n) m)) empty_set ]
          |> self#expr scx

      (** [h \in dom |-> ex] = <<e1, ..., en>> -->
          /\ dom = 1 .. n
          /\ \A h \in dom:  ex = <<e1, ..., en>>[h]
      *)
      | _, Tuple es when is_function_with_explicit_domain x ->
        let scx' = adj scx dummy in
        let h,_,dom,ex = Option.get (extract_domain_from_function x) in
        lAnd [
          (eq dom (range one (Num (string_of_int (length es), "") |> mk))) ;
          (forall ~id:h ~dom:dom ~typ:(get_tybase scx dom)
            (eq ex (fcnapp_u scx' (sh1 y) ix1)))
        ] |> self#expr scx
      | Tuple es, _ when is_function_with_explicit_domain y ->
        let scx' = adj scx dummy in
        let h,_,dom,ex = Option.get (extract_domain_from_function y) in
        lAnd [
          (eq dom (range one (Num (string_of_int (length es), "") |> mk))) ;
          (forall ~id:h ~dom:dom ~typ:(get_tybase scx dom)
            (eq ex (fcnapp_u scx' (sh1 x) ix1)))
        ] |> self#expr scx

      | _, Tuple es when es <> [] ->
        let dom = range one (Num (string_of_int (length es), "") |> mk) in
        lAnd begin
          isAFcn x ::
          (eq (domain x) dom) ::
          (* (forall ~dom:dom ~typ:(get_tybase scx dom) (eq (fcnapp (sh1 x) ix1) (fcnapp_u scx' (sh1 y) ix1))) *)
          (mapi (fun i e -> eq (fcnapp_u scx x (Num (string_of_int (i+1),"") |> mk)) e) es)
        end |> self#expr scx

      | _, Product es ->
        let scx' = adj scx dummy in
        forall
          (equiv
            (mem (sh1 x) ix1)
            (lAnd
              (isAFcn x ::
               eq (domain x) (range one (mk_num (length es))) ::
              (mapi (fun i ex -> mem (fcnapp_u scx' (sh1 x) (mk_num (i+1))) (sh1 ex)) es))) )
        |> self#expr scx
      | Product _, _ ->
        eq y x |> self#expr scx

      | Apply ({core = Internal B.Range}, [a ; b]), Apply ({core = Internal B.Range}, [a' ; c])
        when is_Int scx a && is_Int scx b && is_Int scx a' && is_Int scx c && Expr.Eq.expr a a' ->
        lOr [eq b c ; lAnd [lt b a ; lt c a]] |> self#expr scx

      | _, Except ({core = Except (f, exs1)}, exs2) when Smt.is_term x ->
          (* Apply (o, [x ; Except (f, exs1 @ exs2) @@ y]) |> mk *)
        eq x (Except (f, exs1 @ exs2) @@ y) |> self#expr scx

      (*** BUG: nested Except_apply and Except_dot *)
      | _, Except (f, ((([Except_apply _], b) :: _ ) as exs)) when Smt.is_term x ->
        let exs = map (fun (exp,b) -> match exp with [Except_apply a] -> a,b | _ -> assert false) exs in
        let zs,_ = split exs in
        (* let isb = T.is_bool (snd scx) b in *)
        let isb = T.is_hard_bool b in
        let conn x y = if isb then equiv (boolify x) y else eq x y in       (** PROVE *)
        let scx' = adj scx dummy in
        lAnd [
          isAFcn x ;
          eq (domain f) (domain x) ;
          lAndx (map (fun (a,b) -> implies (mem a (domain f)) (conn (fcnapp_u scx x a) b)) exs) ;
          forall ~dom:(setminus (domain f) (SetEnum zs |> mk)) ~typ:(get_tybase scx (domain f))
            (eq (fcnapp_u scx' (sh1 f) ix1) (fcnapp_u scx' (sh1 x) ix1))
        ] |> self#expr scx
        (* p ex   (** We don't normalize now. We give this equality another chance to be `simplified'. *) *)
      | _, Except (r, [([Except_dot h], b)]) when Smt.is_term x ->
          (* let isb = T.is_bool (snd scx) b in *)
          let isb = T.is_hard_bool b in
          let conn x y = if isb then equiv (boolify x) y else eq x y in       (** PROVE *)
          let scx' = adj scx dummy in
          lAnd [
            isAFcn x ;
            eq (domain x) (domain r) ;
            implies (mem (str h) (domain r)) (conn (fcnapp_u scx x (str h)) b) ;
            forall ~dom:(setminus (domain r) (SetEnum [str h] |> mk)) ~typ:(get_tybase scx (domain r))
              (eq (fcnapp_u scx' (sh1 r) ix1) (fcnapp_u scx' (sh1 x) ix1))
          ] |> self#expr scx
      | Except _, _ when Smt.is_term y ->
        eq y x |> self#expr scx

      (** does not Boolify IF ... = IF ... *)
      (* | Except (f, [([Except_apply a], e1)]), Except (g, [([Except_apply b], e2)]) ->
          self#expr scx (lAnd [ eq (domain f) (domain g) ;
                          forall ~dom:(domain f) (eq
                                  (ifte (eq ix1 (sh1 a)) (sh1 e1) (fcnapp (sh1 f) ix1))
                                  (ifte (eq ix1 (sh1 b)) (sh1 e2) (fcnapp (sh1 g) ix1)))]) *)

      | _, Record fes when Smt.is_term x ->
        let fs,_ = split fes in
        let cdom = eq (domain x) (SetEnum (map str fs) |> mk) in
        let conn c x y = if c then equiv (boolify x) y else eq x y in       (** PROVE *)
        lAnd (isAFcn x :: cdom ::
            (* (map (fun f -> mem (str f) (domain x)) fs) @ *)
            (map (fun (h,e) ->
              (* eq (fcnapp_u scx x (str h)) e *)
              conn (T.is_hard_bool e) (fcnapp_u scx x (str h)) e
              ) fes))
        |> self#expr scx
      | Record _, _ when Smt.is_term y ->
        eq y x |> self#expr scx

      (* | _, Tuple es -> lAnd (mapi (fun i e -> eq (fcnapp x (Num (string_of_int (i+1),"") |> mk)) e) es)
      | Tuple es, _ -> lAnd (mapi (fun i e -> eq (fcnapp y (Num (string_of_int (i+1),"") |> mk)) e) es) *)

      (* | If (c1,t1,f1), If (c2,t2,f2) -> self#expr scx (lAnd [implies c1 (conj (implies c2 (eq t1 t2))
                                                                       (implies (neg c2) (eq t1 f2))) ;
                                                      implies (neg c1) (conj (implies c2 (eq f1 t2))
                                                                             (implies (neg c2) (eq f1 f2)))]) *)

      | _, If (c,t,f) when Smt.is_term x ->
        ifte c (eq x t) (eq x f) |> self#expr scx
      | If (c,t,f), _ when Smt.is_term y ->
        ifte c (eq t y) (eq f y) |> self#expr scx

      | Num _, Apply ({core = Internal B.Minus}, [n ; ({core = Num _} as y)]) ->
        eq n (plus x y) |> self#expr scx
      | Apply ({core = Internal B.Minus}, [n ; ({core = Num _} as x)]), Num _ ->
        eq n (plus x y) |> self#expr scx

      (* | _, Apply ({core = Internal B.Len}, [{core = Apply ({core = Internal B.Tail}, [s])}]) ->
          implies (neg (eq s empty_tuple))
                  (eq x (minus (len s) one))
                  |> self#expr scx *)
            (** x = Len(s) --> x \in Nat /\ DOMAIN s = 1 .. x *)

      | _, Apply ({core = Internal B.Len}, [s]) ->
        lAnd [mem x nats ; eq (domain s) (range one x)] |> self#expr scx
          (* self#expr scx (implies (isASeq s)
                          (lAnd [mem x nats ; eq (domain s) (range one x)])) *)
          (* self#expr scx (implies (exists ~dom:nats (eq (domain (sh1 s)) (range one ix1)))
                          (lAnd [mem x nats ; eq (domain s) (range one x)])) *)

      (** x = Append(s, ex) -->
            /\ isAFcn(x)
            /\ (DOMAIN x) = 1 .. Len(s) + 1
            /\ \A z \in 1 .. Len(s):  x[z] = s[z]
            /\ x[Len(s) + 1] = ex
      *)
      | _, Apply ({core = Internal B.Append}, [s ; ex]) ->
          let dom1 = range one (len s) in
          lAnd [
            isAFcn x ;
            eq (domain x) (range one (plus (len s) one)) ;
            forall ~dom:dom1 ~typ:(get_tybase scx dom1)
                (eq (fcnapp (sh1 x) ix1) (fcnapp (sh1 s) ix1)) ;
            eq (fcnapp x (plus (len s) one)) ex
          ] |> self#expr scx

      (** x = Tail(s) -->
            s # <<>> =>
                /\ isAFcn(x)
                /\ (DOMAIN x) = 1 .. Len(s) - 1
                /\ \A z \in 1 .. Len(s) - 1:
                    x[z] = s[z + 1]
      *)
      | _, Apply ({core = Internal B.Tail}, [s]) ->
          let dom = range one (minus (len s) one) in
          implies
            (neg (eq s empty_tuple))
            (lAnd [
              isAFcn x ;
              eq (domain x) dom ;
              forall ~dom:dom ~typ:(get_tybase scx dom)
                  (eq (fcnapp (sh1 x) ix1) (fcnapp (sh1 s) (plus ix1 one)))
              ])
            |> self#expr scx

      (** x = Cat(s, t) -->
            /\ isAFcn(x)
            /\ (DOMAIN x) = 1 .. Len(s) + Len(t)
            /\ \A z \in 1 .. Len(s):  x[z] = s[z]
            /\ \A z \in 1 .. Len(t):  x[Len(s) + z] = t[z]
            /\ \A z \in Len(s) + 1 .. Len(s) + Len(t):
                x[z] = t[z - Len(s)]

          NB: The last two conjuncts are redundant but including both makes
          more proofs succeed. *)
      | _, Apply ({core = Internal B.Cat}, [s ; t]) ->
          let dom = range one (plus (len s) (len t)) in
          lAnd [
            isAFcn x ;
            eq (domain x) dom ;
            (* forall ~dom:dom (eq (fcnapp (sh1 x) ix1)
                               (ifte (leq one (len (sh1 s))) (fcnapp (sh1 s) ix1) (fcnapp (sh1 t) (minus ix1 (len (sh1 s))))) )  *)
            forall ~dom:(range one (len s)) ~typ:(Some T.Int)
                (eq (fcnapp (sh1 x) ix1) (fcnapp (sh1 s) ix1)) ;
            forall ~dom:(range one (len t)) ~typ:(Some T.Int)
                (eq (fcnapp (sh1 x) (plus (len (sh1 s)) ix1)) (fcnapp (sh1 t) ix1)) ;
            forall ~dom:(range (plus (len s) one) (plus (len s) (len t))) ~typ:(Some T.Int)
                (eq (fcnapp (sh1 x) ix1)
                    (fcnapp (sh1 t) (minus ix1 (len (sh1 s)))))
          ] |> self#expr scx

      (** x = SubSeq(s, m, n) -->
            /\ isAFcn(x)
            /\ (DOMAIN x) = 1 .. 1 + n - m
            /\ \A z \in m .. n:  x[1 + z - m] = s[z]
      *)
      | _, Apply ({core = Internal B.SubSeq}, [s ; m ; n]) ->
          let dom = range one (minus (plus one n) m) in
          lAnd [
            isAFcn x ;
            eq (domain x) dom ;
            (* forall ~dom:dom (eq (fcnapp (sh1 x) ix1) (fcnapp (sh1 s) (minus (plus ix1 (sh1 m)) one)))  *)
            forall ~dom:(range m n) ~typ:(Some T.Int)
                (eq (fcnapp (sh1 x) (minus (plus one ix1) (sh1 m)))
                   (fcnapp (sh1 s) ix1))
          ] |> self#expr scx

      | Apply ({core = Internal B.Len
                     | Internal B.Append
                     | Internal B.Tail
                     | Internal B.Cat
                     | Internal B.SubSeq}, _), _ ->
          eq y x |> self#expr scx

      | Tuple _, _ ->
          eq y x |> self#expr scx

      | Opaque _, Lambda (vs, ex) ->
        let spin (h,s) r = match s with Shape_expr -> (Opaque h.core |> mk) :: r | Shape_op _ -> r in
        let vs = fold_right spin vs [] in
        let ex = fold_right (fun v e -> e <~ v) vs ex in
        (* let x = Apply (x, vs) |> mk in *)
        let x = FcnApp (x, vs) |> mk in
        eq x ex |> self#expr scx
      | _ ->
        eq x y
    in
    match e.core with
    (* | If (c,t,f) when (!Smt.mode = Spass || !Smt.mode = Fof) && T.is_hard_bool c && T.is_hard_bool t && T.is_hard_bool f ->
        let c = Smt.sf#simpl (snd scx) c in
        if is_true c then t else conj (implies c t) (implies (neg c) f) *)
    (* | Apply ({core = Internal B.Mem}, [x ; {core = Internal B.BOOLEAN}]) when T.is_hard_bool x ->
        lOr [Boolify.mk_bool x ; neg (Boolify.mk_bool x)] |> self#expr scx *)
    (* | Internal B.BOOLEAN -> SetEnum [tla_true ; tla_false] |> mk *)
    (* | Apply ({core = Internal B.Neq}, ([x ; {core = SetEnum []}]
       | [{core = SetEnum []} ; x])) when is_conc e ->
        implies (eq x empty_set) tla_false |> gr1p scx *)

    (** x # {}  --> \E y \in x: TRUE *)
    | Apply ({core = Internal B.Neq}, ([x ; {core = SetEnum []}] | [{core = SetEnum []} ; x]) ) ->
      exists ~dom:x tla_true |> self#expr scx

    (** Extensionality contraction *)
    (* | Quant (Forall, [_,_,No_domain], {core = Apply ({core = Internal B.Equiv},
        [{core = Apply ({core = Internal B.Mem}, [{core = Ix 1} ; x])} ;
         {core = Apply ({core = Internal B.Mem}, [{core = Ix 1} ; y])}
        ])}) ->
        eq x y *)

    | Apply ({core = Internal op} as o, [x ; y]) ->
      let x = self#expr scx x in
      let y = self#expr scx y in
      begin
        match op, x.core, y.core with
        | B.Mem, _, _ ->
          rw_mem x y

        | (B.Eq | B.Equiv), _, Choose (h, None, ex) ->
    (* Util.eprintf "Choo: %a : %s" (print_prop ()) (sh1 (sh1 ex)) (typ_to_str e) ; *)
            (* add_choose (fresh_name ()) cx x ;  *)            (*** FIX CHOOSE determinacy ***)
          implies (exists ~id:h ex) (ex <~ x) |> self#expr scx
        | (B.Eq | B.Equiv), Choose _, _ ->
          Apply (o, [y ; x]) |> mk |> self#expr scx

        | B.Equiv, If (c1,t,u), If (c2,v,w) when Expr.Eq.expr c1 c2 ->
          ifte c1 (equiv t v) (equiv u w) |> self#expr scx
        | B.Equiv, If (c,t,u), _
          when List.exists (fun e -> is_true e || is_false e) [t;u] ->
          ifte c (equiv t y) (equiv u y) |> self#expr scx
        | B.Equiv, _, If (c,t,u)
          when List.exists (fun e -> is_true e || is_false e) [t;u] ->
          ifte c (equiv x t) (equiv x u) |> self#expr scx

        | (B.Eq | B.Equiv), If (c1,t1,f1), If (c2,t2,f2) ->
          apply2 op x y
        | B.Equiv, _, If (c,t,f) when Smt.is_term x ->
          ifte_bool c (equiv x t) (equiv x f) |> self#expr scx
        | B.Equiv, If (c,t,f), _ when Smt.is_term y ->
          ifte_bool c (equiv t y) (equiv f y) |> self#expr scx

        | B.Eq, _, _ ->
          rw_eq x y

        | (B.Lt | B.Lteq), _, If (c,t,f) when Smt.is_term x ->
          ifte_bool c (apply2 op x t) (apply2 op x f) |> self#expr scx
        | (B.Lt | B.Lteq), If (c,t,f), _ when Smt.is_term y ->
          ifte_bool c (apply2 op t y) (apply2 op f y) |> self#expr scx
        | (B.Plus | B.Minus | B.Times | B.Exp), _, If (c,t,f) when Smt.is_term x ->
          ifte c (apply2 op x t) (apply2 op x f) |> self#expr scx
        | (B.Plus | B.Minus | B.Times | B.Exp), If (c,t,f), _ when Smt.is_term y ->
          ifte c (apply2 op t y) (apply2 op f y) |> self#expr scx

        | (B.Lt | B.Lteq), If (c1,t1,f1), If (c2,t2,f2)
          when Expr.Eq.expr c1 c2 ->
          ifte_bool c1 (Apply (o, [t1 ; t2]) @@ e) (Apply (o, [f1 ; f2]) @@ e)
          |> self#expr scx
        | (B.Plus | B.Minus | B.Times | B.Exp), If (c1,t1,f1), If (c2,t2,f2)
          when Expr.Eq.expr c1 c2 ->
          ifte c1 (Apply (o, [t1 ; t2]) @@ e) (Apply (o, [f1 ; f2]) @@ e)
          |> self#expr scx

        (* | (B.Lt | B.Lteq), _, Apply ({core = Internal B.Len}, [{core = Apply ({core = Internal B.Tail}, [s])}]) ->
            self#expr scx (lAnd [neg (eq x empty_tuple) ; Apply (o, [x ; minus (len s) one]) |> mk])
        | (B.Lt | B.Lteq), Apply ({core = Internal B.Len}, [{core = Apply ({core = Internal B.Tail}, [s])}]), _ ->
            self#expr scx (lAnd [neg (eq y empty_tuple) ; Apply (o, [minus (len s) one ; y]) |> mk]) *)

        (* | B.Lteq, _, _ -> implies (lAnd [mem x ints ; mem y ints]) (opq "<=" [x ; y]) *)
        (* | B.Lt  , _, _ -> implies (lAnd [mem x ints ; mem y ints]) (opq "<" [x ; y]) *)

        | B.Conj, _, _ ->
          lAnd [x ; y] |> self#expr scx
        | B.Disj, _, _ ->
          lOr [x ; y] |> self#expr scx
        (* | B.Implies, _, _ when is_true (Smt.sf#simpl (snd scx) y) -> tla_true *)

        | B.Implies, _, _ when is_true (Smt.sf#simpl (snd scx) x) ->
          build y
        | B.Implies, If (c1,t,u), If (c2,v,w) when Expr.Eq.expr c1 c2 ->
          ifte c1 (implies t v) (implies u w) |> self#expr scx
        | B.Implies, If (c,t,u), _
          when List.exists (fun e -> is_true e || is_false e) [t;u] ->
          ifte c (implies t y) (implies u y) |> self#expr scx
        | B.Implies, _, If (c,t,u)
          when List.exists (fun e -> is_true e || is_false e) [t;u] ->
          ifte c (implies x t) (implies x u) |> self#expr scx

        (* | B.Implies, _, _ -> Apply (o, [Smt.sf#simpl (snd scx) x ; y]) |> mk *)

        | B.Neq, _, _ ->
          neg (self#expr scx (eq x y))
        | B.Notmem, _, _ ->
          neg (self#expr scx (mem x y))

        (** {e1, ..., en} \subseteq S  -->  e1 \in S /\ ... /\ en \in S *)
        | B.Subseteq, SetEnum es, _ ->
          lAnd (map (fun e -> mem e y) es) |> self#expr scx

        (** S \subseteq T  -->  \A x \in S: x \in T *)
        | B.Subseteq, _, _ ->
          forall ~dom:x ~typ:(get_tybase scx x) (mem ix1 (sh1 y)) |> self#expr scx

        (* | B.BSeq, _, _          -> opq "BSeq"      (map (self#expr scx) [x ; y])
        | B.Cat, _, _           -> opq "Cat"       (map (self#expr scx) [x ; y])
        | B.Append, _, _        -> (apply B.Cat x (Tuple [y] |> mk)) |> self#expr scx
        | B.SelectSeq, _, _     -> opq "SelectSeq" (map (self#expr scx) [x ; y]) *)

        | B.OneArg, _, _  -> opq "OneArg"  (map (self#expr scx) [x ; y])
        | B.Extend, _, _  -> opq "Extend"  (map (self#expr scx) [x ; y])
        | B.Print, _, _   -> opq "Print"   (map (self#expr scx) [x ; y])
        | B.Assert, _, _  -> opq "Assert"  (map (self#expr scx) [x ; y])
        | B.TLCSet, _, _  -> opq "TLCSet"  (map (self#expr scx) [x ; y])
        | B.SortSeq, _, _ -> opq "SortSeq" (map (self#expr scx) [x ; y])
        | _ ->
          Apply (o, [x ; y]) |> mk
      end

    | Apply ({core = Internal op} as o, [ex]) ->
      let ex = self#expr scx ex in
      begin
        match op, ex.core with
        | _, If (c,t,f) ->
          self#expr scx (ifte c (apply1 op t) (apply1 op f))
        | B.Neg, _ -> neg ex
        | B.DOMAIN, Fcn (bs,_) ->
            let bs = Expr.T.unditto bs in
            let rec doms = function
              | (_,_,Domain d) :: bs -> d :: doms bs
              | [] -> []
              | _ -> assert false
            in
            begin match doms bs with
              | [] -> assert false
              | [ex] -> self#expr scx ex
              | exs -> self#expr scx (Tuple exs |> mk)
            end
        | B.DOMAIN, Tuple es ->
          range one (Num (string_of_int (length es), "") |> mk)
        | B.DOMAIN, Record fes ->
          let fs,_ = List.split fes in
          SetEnum (map str fs) |> mk
        | B.DOMAIN, Except (f,_) ->
          let f = self#expr scx f in
          apply1 op f
        (*| B.DOMAIN, Apply ({core = Internal B.Tail}, [s]) ->
            self#expr scx (ifte (eq s empty_tuple) empty_set (range one (minus (len s) one))) *)
        | B.DOMAIN, Apply ({core = Internal B.Tail}, [s]) ->
          self#expr scx (range one (minus (len s) one))
        | B.DOMAIN, Apply ({core = Internal B.Append}, [s ; _]) ->
          self#expr scx (range one (plus (len s) one))
        (* sm: added 2019-02-19 *)
        | B.DOMAIN, Apply ({core = Internal B.Cat}, [s ; t]) ->
          self#expr scx (range one (plus (len s) (len t)))
        (* sm: added 2019-02-21 *)
        | B.DOMAIN, Apply ({core = Internal B.SubSeq}, [s ; m ; n]) ->
          self#expr scx (range one (plus one (minus n m)))
        | B.SUBSET, _ -> apply1 op ex
        | B.UNION, _  -> apply1 op ex
        | B.Uminus, _ -> apply1 op ex
        (* | B.Prime, _  -> apply1 B.Prime  (self#expr scx ex) *)
        (* | B.Prime, _ ->
            begin match ex.core with
            | Apply ({core = Ix n}, es)      -> self#expr scx (opq (prime (lookup_id cx n)) es)
            | Apply ({core = Opaque id}, es) -> self#expr scx (opq (prime id) es)
            | Ix n                           -> self#expr scx (opq (prime (lookup_id cx n)) [])
            | Opaque id                      -> self#expr scx (opq (prime id) [])
            | _                              -> Util.bug "src/backend/ground.ml. Prime expression."
            end *)

        | B.Unprimable, _ -> self#expr scx ex
        | B.Irregular, _ -> self#expr scx ex
        | B.Head, _ -> fcnapp ex one
        (* | B.Seq, _  -> opq "Seq"  [self#expr scx ex] *)
        (* | B.Seq, _  -> apply1 B.UNION (SetOf (Arrow (apply B.Range one ix1, (sh1 ex)) |> mk, [fresh_name () |> mk, Unknown, Domain nats]) |> mk) *)
        | B.Len, Tuple es -> Num (string_of_int (length es), "") |> mk
        | B.Len, Apply ({core = Internal B.Tail}, [s]) ->
          ifte (eq s empty_tuple) zero (minus (len s) one) |> self#expr scx   (* Given that Tail(<<>>) = <<>> *)
        | B.Len, Apply ({core = Internal B.Append}, [ex ; _]) ->
          plus (len ex) one |> self#expr scx
        | B.Len, Apply ({core = Internal B.Cat}, [x ; y]) ->
          plus (len x) (len y) |> self#expr scx
        | B.Len, Apply ({core = Internal B.SubSeq}, [s ; m ; n]) ->
          ifte (lAnd [mem m ints ; mem n ints])
              (ifte (leq m n) (plus (minus n m) one) zero)
              (unspec scx e)
            |> self#expr scx

  (*
        | B.Len, Fcn ([_,_,Domain ({core = Apply ({core = Internal B.Range}, [{core = Num("1","")}; n])})], _) ->
          ifte (mem n nats) n (unspec scx e) |> self#expr scx
  *)
        | B.Len, _ when is_function_with_explicit_domain ex ->
          let h,n,dom,ex = Option.get (extract_domain_from_function ex) in
  (*
            ifte (eq dom empty_set)
                            zero (ifte (mem n nats) n (unspec scx e)) |> self#expr scx
  *)
          ifte (mem n nats) n (unspec scx e) |> self#expr scx
        | B.Len, Except (s,_) ->
          len s |> self#expr scx
        | B.Tail, Tuple (_ :: es) ->
          Tuple (map (self#expr scx) es) |> mk
        (* | B.Len, _  -> opq "Len"  [self#expr scx ex] *)
        (* | B.Tail, _ -> opq "Tail" [self#expr scx ex] *)

        | B.PrintT, _        -> opq "PrintT"        [self#expr scx ex]
        | B.TLCGet, _        -> opq "TLCGet"        [self#expr scx ex]
        | B.Permutations, _  -> opq "Permutations"  [self#expr scx ex]
        | B.RandomElement, _ -> opq "RandomElement" [self#expr scx ex]
        | B.ToString, _      -> opq "ToString"      [self#expr scx ex]
        | _ -> Apply (o, [ex]) |> mk
      end
    | Apply ({core = Internal op}, es) ->
      let es = map (self#expr scx) es in
      begin
        match op, es with
        | B.JavaTime,  []      -> opq "JavaTime" []
        | B.Any,       []      -> opq "Any" []
        (* | B.SubSeq, [s ; n ; m] when Expr.Eq.expr n m -> self#expr scx (Tuple [fcnapp s n] |> mk) *)
        | _ -> Apply (Internal op |> mk, es) |> mk
      end
    | Apply ({core = Opaque "tla__isAFcn"}, [ex]) ->
      let ex = self#expr scx ex in
      begin
        match ex.core with
        | Fcn _ -> tla_true
        | Tuple _ -> tla_true
        | Record _ -> tla_true
        | Except _ -> tla_true
        | Apply ({core = Internal B.Append}, _)
        | Apply ({core = Internal B.Cat}, _)
        | Apply ({core = Internal B.Tail}, _)
        | Apply ({core = Internal B.SubSeq}, _)
        | Apply ({core = Internal B.SelectSeq}, _) -> tla_true
        | If (c,t,f) -> self#expr scx (ifte_bool c (isAFcn t) (isAFcn f))
        | _ -> isAFcn ex
      end
    | Apply ({core = Opaque "boolify"}, [ex]) when T.is_hard_bool ex ->
      self#expr scx ex
    | Apply ({core = Opaque "boolify"} as op, [ex]) ->
      let ex = self#expr scx ex in
      begin
        match ex.core with
        | If (c, t, u) ->
          If (c, boolify t, boolify u) |> mk
        | _ ->
          Apply (op, [ex]) |> mk
      end
    | Apply ({core = Opaque "tla__fcnapp"} as op, [f ; {core = If (c,t,u)}]) ->
      ifte c (Apply (op, [f ; t]) |> mk) (Apply (op, [f ; u]) |> mk)
    | Apply (e, es) ->
      let e = self#expr scx e in
      let es = map (self#expr scx) es in
      Apply (e, es) |> mk

    | Dot ({core = Record rs} as r, h)
    | FcnApp ({core = Record rs} as r, [{core = String h}]) ->
      begin
        try
          let _,ex = List.find (fun (f,_) -> h = f) rs in
          ex
        with _ -> (* add_field h ; dot (self#expr scx r) h *)
          opq "tla__unspec" [r ; String h %% []]
      end
      |> self#expr scx
    | Dot ({core = Except (r, [([Except_dot f], ex)])}, h)
    | FcnApp ({core = Except (r, [([Except_dot f], ex)])}, [{core = String h}]) ->
      (* self#expr scx (ifte (conj (eq (str f) (str h)) (isFldOf (str f) r)) ex (dot r h)) *)
      ifte (eq (str f) (str h)) ex (dot r h) |> self#expr scx

    | Dot ({core = If (c,t,f)}, h) ->
      ifte c (dot t h) (dot f h) |> self#expr scx
    | Dot (ex, h) ->
      FcnApp (ex, [String h %% []]) @@ e |> self#expr scx

    (** [!Smt.typesystem_mode = 2] means ignore domain checking *)
    | FcnApp (f, es) when !Smt.typesystem_mode = 2 ->
      let f = self#expr scx f in
      let es = map (self#expr scx) es in
      begin
        match f.core, es with
        | Fcn ([_,_,Domain dom], ex), [x] ->
          (ex <~ x) |> self#expr scx
        | Except (f, [([Except_apply y], ex)]), [x] ->
          let c2 = eq x y
            |> self#expr scx
            |> Smt.sf#simpl (snd scx)
          in
          begin
            if is_true c2 then ex
            else ifte c2 ex (fcnapp_u scx f x)
          end |> self#expr scx
        | If (c,t,f), es ->
          ifte c
            (FcnApp (t, es) |> mk)
            (FcnApp (f, es) |> mk)
          |> self#expr scx
        | Tuple ts, [{core = Num (i,"")}]
          when 1 <= int_of_string i && int_of_string i <= length ts ->
          (try List.nth ts ((int_of_string i) - 1) with e -> raise e)
          |> self#expr scx
        | _, [x] ->
          (fcnapp_u scx f x) |> self#expr scx
        | _ ->
          FcnApp (f, es) |> mk
      end
    | FcnApp (f, es) ->
      let f = self#expr scx f in
      let es = map (self#expr scx) es in
      begin
        match f.core, es with
        | Fcn ([_,_,Domain dom], ex), [x] ->
          let ex = ex <~ x in
          let c = mem x dom
            |> Smt.sf#simpl (snd scx)
          in
          ifte c ex (opq "tla__unspec" (f::es)) |> self#expr scx
        | Except (f, [([Except_apply y], ex)]), [x] ->
          let c1 = mem x (domain f)
            |> self#expr scx
            |> Smt.sf#simpl (snd scx)
          in
          let c2 = eq x y
            |> self#expr scx
            |> Smt.sf#simpl (snd scx)
          in
          begin
            if is_true c1 then
              if is_true c2 then ex
              else ifte c2 ex (fcnapp_u scx f x)
            else
              ifte c1
                (ifte c2 ex (fcnapp_u scx f x))
                (opq "tla__unspec" (f::es))
          end |> self#expr scx

        (** (IF c THEN t ELSE f)[es] --> IF c THEN t[es] ELSE f[es] *)
        | If (c,t,f), es ->
          ifte c
            (FcnApp (t, es) |> mk)
            (FcnApp (f, es) |> mk)
          |> self#expr scx
              (** <<e1, ..., en>>[i] --> ei *)
              | Tuple ts, [{core = Num (i,"")}]
                      when 1 <= int_of_string i && int_of_string i <= length ts ->
          (try List.nth ts ((int_of_string i) - 1) with e -> raise e)
          |> self#expr scx

        (** Append(s, ex)[i] -->
            IF i \in 1..Len(s)
                THEN s[i]
                ELSE (IF i = Len(s) + 1
                    THEN ex
                    ELSE unspec(Append(s, ex), i))
        *)
        | Apply ({core = Internal B.Append}, [s ; ex]), [i] ->
          ifte (mem i (range one (len s)))
                          (fcnapp s i)
                          (ifte (eq i (plus (len s) one)) ex (unspec scx e))
                      |> self#expr scx

        (** Tail(s)[i] -->
            IF i \in 1 .. Len(s) - 1
                THEN s[i + 1]
                ELSE unspec(Tail(s), i)
        *)
        | Apply ({core = Internal B.Tail}, [s]), [i] ->
          ifte (mem i (range one (minus (len s) one)))
                          (fcnapp s (plus i one))
                          (unspec scx e)
                      |> self#expr scx

        (** SubSeq(s,m,n)[i] -->
            IF i \in 1 .. 1 + n - m
                THEN s[i + m - 1]
                ELSE unspec(SubSeq(s, m, n), i)
        *)
        | Apply ({core = Internal B.SubSeq}, [s ; m ; n]), [i] ->
          ifte (mem i (range one (minus (plus one n) m)))
                          (fcnapp s (minus (plus i m) one))
                          (unspec scx e)
                      |> self#expr scx
        | Apply ({core = Internal B.Cat}, [s ; t]), [i] ->
          ifte (mem i (range one (len s)))
            (fcnapp s i)
            (ifte (mem i (range (plus (len s) one) (plus (len s) (len t))))
              (fcnapp t (minus i (len s)))
              (unspec scx e))
                      |> self#expr scx
              (** f[x] -->
                    IF x \in DOMAIN f
                        THEN tla__fcnapp(f, x)
                        ELSE tla__unspec(f, x)
              *)
              | _, [x] ->
          ifte (mem x (domain f))
            (fcnapp_u scx f x)
            (opq "tla__unspec" (f::[x]))
          |> self#expr scx
        | _ ->
          FcnApp (f, es) |> mk
      end

    (** [_ \in {} |-> _] --> <<>> *)
    | Fcn ([_,_,Domain {core = SetEnum []}], _) ->
      empty_tuple

    | Case ([(c, ex)], None) ->
      let c = c
        |> self#expr scx
        |> Smt.sf#simpl (snd scx)
      in
      let ex = self#expr scx ex in
      if is_true c then build ex else ifte c ex (unspec scx e)
      |> self#expr scx
    | Case ([(c, ex)], Some o) ->
      ifte c ex o |> self#expr scx
    (* | Case ((c, ex) :: es, None) -> (* self#expr scx (ifte c ex (Case (es, None) |> mk)) *) *)
    (* | Case (es, None) ->
        let (cs,es) = split es in
        let p = lAnd (hd cs :: (map neg (tl cs))) in
        self#expr scx (ifte p (hd es) (Case (combine (tl cs) (tl es), None) |> mk)) *)
    | Case (es, other) ->
      let cs,es = split es in
      let c,cs = hd cs, tl cs in
      let e,es = hd es, tl es in
      ifte (lAnd (c :: (map neg cs))) e (Case (combine cs es, other) |> mk)
      |> self#expr scx

    | Quant (q, ((v,k,Domain {core = SetEnum es}) :: bs), ex) ->
      (* let scx', b' = self#bounds scx [b] in
      let b = match b' with [b] -> b | _ -> assert false in *)
      let es = map (self#expr scx) es in
      let scx',_ = self#bounds scx [(v,k,No_domain)] in

      (** Incorporate [bs] to body [ex] *)
      let ex = match bs with
        | [] -> ex
        | bs -> let _,bs = app_bounds (shift 1) bs in
            Quant (q, bs, ex) @@ e
      in
      let es = map (fun a -> ex <~ a) es in
      let ex = match q, es with
        | Forall, [] -> tla_true
        | Exists, [] -> tla_false
        | _, [ex] -> ex
        | Forall, _ -> lAnd es
        | Exists, _ -> lOr es
      in
      ex |> self#expr scx'

    (** [Quant] assumption: already [Expr.T.unditto] *)
    (* | Quant (q, b :: bs, ex) -> *)
    | Quant (q, ((v,_,_) as b) :: bs, ex) ->
(* Util.eprintf "{rw} %a" (Expr.Fmt.pp_print_expr (snd scx, Ctx.dot)) e ; *)
      (** Partition body [ex] to obtain typing hypotheses for variable [v].
          [ths] = typing hypotheses for variable [v]
          [hs] = other hypotheses
          [c] = conclusion *)
      let partition_body scx q v ex =
        match q with
        | Forall ->
          (** TODO: add as simple-facts only typing hypotheses for the bounded variable. *)
          let hs,c = Smt.deimpl ex in
          let hs = List.flatten (map Smt.deconj hs) in
          let ths,hs = List.partition (Smt.is_typhyp ~var:v.core (snd scx)) hs in
          ths, hs, c
        | Exists ->
          let es = Smt.deconj ex in
          let ths,es = List.partition (Smt.is_typhyp ~var:v.core (snd scx)) es in
          ths, [], lAndx es
      in

      (** Pass domains from bounds [bs] to body [ex].
          The resulting [bs] has [No_domain]s.
          `[\A x \in S:  ex] --> [\A x:  x \in S => ex]`
      *)
      (* let unbound q bs ex =
        let bs,ds = Smt.unb bs in
        let conn q = match q with Forall -> implies | Exists -> conj in
        let ex = if ds = [] then ex else (conn q) (lAndx ds) ex in
        bs,ex,ds
      in *)

      (** Incorporate [bs] to body [ex] *)
      let ex = match bs with
        | [] -> ex
        | bs -> let _,bs = app_bounds (shift 1) bs in
            Quant (q, bs, ex) @@ e
      in

(* Util.eprintf "{rw'} %a" (Expr.Fmt.pp_print_expr (snd scx, Ctx.dot)) (Quant (q,[b],ex) @@ e)  ; *)

      (** Now [e] = [Quant (q, [b], ex)] *)
      let scx', b' = self#bounds scx [b] in
      let b = match b' with [b] -> b | _ -> assert false in

      let ths,hs,c = partition_body scx q v ex in

      (* let bs',ds = Smt.unb [b] in
      let ds = map (self#expr scx') ds in *)
(* Util.eprintf "... b = %a" (Expr.Fmt.pp_print_expr (snd scx', Ctx.dot)) (lAnd ds) ; *)

      (* let bs,ex,ds = unbound q [b] ex in *)
      let bs,ds = Smt.unb [b] in
      (* let b = match b' with [b] -> b | _ -> assert false in *)

      let eval_and_push scx es =
        List.fold_left (fun (ds,n) e ->
          let e = self#expr scx' e in
          let n' = Smt.sf#push (snd scx) [e] in
          (ds @ [e]), n+n'
        ) ([],0) es
      in

      let ds,n1 = eval_and_push scx' ds in
      let ths,n2 = eval_and_push scx' ths in
      let hs,n3 = eval_and_push scx' hs in
      (* let ds = map (self#expr scx') ds in
      let ths = map (self#expr scx') ths in
      let hs = map (self#expr scx') hs in
      let n1 = Smt.sf#push (snd scx') ds in
      let n2 = Smt.sf#push (snd scx') ths in
      let n3 = Smt.sf#push (snd scx') hs in *)
      let c = self#expr scx' c in
      Smt.sf#pop (n1 + n2 + n3);

      (** Reassemble body [ex] *)
      let ex = match q, ds @ ths @ hs with
        | _, [] -> c
        | Forall, hs -> implies (lAndx hs) c
        | Exists, hs -> lAndx (hs @ [c])
      in
      (* let conn q = match q with Forall -> implies | Exists -> conj in *)
      (* let ex = if ds = [] then ex else (conn q) (lAndx ds) ex in *)

      let e = Quant (q, bs, ex) @@ e in

      (** Rewrite according to bound domain in [b] *)
      (* let e = match b with
        | v, k, Domain ({core = SetEnum []}) ->
            tla_true
        | v, k, Domain ({core = SetEnum es}) ->
            let es = map (fun a -> ex <~ a) es in
            let ex = match q, es with
            (* | _, [] -> tla_true *)
            | _, [ex] -> ex
            | Forall, _ -> lAnd es
            | Exists, _ -> lOr es
            in
            ex |> self#expr scx'
        (* | Apply ({core = Internal B.Setminus}, [(* {core = SetEnum _} as *) s ; t]) ->
            let bs = (v, k, Domain s) :: tl bs in
            let st = neg (mem (Ix 1 |> mc <<< typ v) (app_expr (shift 1) t)) in
            let ex = match q with Forall -> implies st ex | Exists -> conj st ex in
            gr1 cx (Quant (q, bs, gr1 (add_bs_ctx bs cx) ex) |> mk) *)
        | _ ->
            (* let bs,ex,ds = unbound q [b] ex in *)
            let bs,ds = Smt.unb [b] in
            (* let b = match b' with [b] -> b | _ -> assert false in *)

            let ds = map (self#expr scx') ds in
            let nf = Smt.sf#push (snd scx') ds in
            let ex = self#expr scx' ex in
            Smt.sf#pop nf;

            let conn q = match q with Forall -> implies | Exists -> conj in
            let ex = if ds = [] then ex else (conn q) (lAndx ds) ex in
            Quant (q, bs, ex) @@ e
      in *)

      e

    | Except (f, [[Except_apply a],b]) ->
      let f = self#expr scx f in
      let a = self#expr scx a in
      let b = self#expr scx b in
      Except (f, [[Except_apply a], b]) |> mk

    (* | If (c,t,f)
        when (!Smt.mode = Spass || !Smt.mode = Fof)
          && T.is_hard_bool c && T.is_hard_bool t && T.is_hard_bool f ->
        let c = Smt.sf#simpl (snd scx) c in
        if is_true c then t else conj (implies c t) (implies (neg c) f) *)
    | If (c,t,f) ->
      let c = c
        |> Smt.sf#simpl (snd scx)
        |> self#expr scx
        |> Smt.sf#simpl (snd scx)
        |> Rewrite_trivial.rw
      in
      let t =
        let n = Smt.sf#push (snd scx) [c] in
        let t = build t |> self#expr scx in
        Smt.sf#pop n;
        t
      in
      let f =
        let n = Smt.sf#push (snd scx) [neg c] in
        let f = build f |> self#expr scx in
        Smt.sf#pop n;
        f
      in
      if (!Smt.mode = Smt.Spass || !Smt.mode = Smt.Fof)
        && T.is_hard_bool c
        && T.is_hard_bool t
        && T.is_hard_bool f
      then conj (implies c t) (implies (neg c) f)
      else
        begin
          if is_true c then t else
          if is_false c then f else
            ifte c t f
        end |> Rewrite_trivial.rw

    | List (b, es) ->
      let is_if e = match e.core with If _ -> true | _ -> false in
      let split_if e = match e.core with If (c,t,u) -> (c,(t,u)) | _ -> assert false in
      let es = map (self#expr scx) es in
      let ifs,rest = partition is_if es in
      if length ifs > 0 then begin
        let cs,tus = map split_if ifs |> split in                           (** cs = conditions, tus = (t,u) list *)
        if length ifs > 1 && for_all (fun x -> Expr.Eq.expr (hd cs) x) (tl cs) then           (** all conditions are equal *)
          let ts,us = split tus in
          let ife = ifte (hd cs) (List (b, ts) |> mk) (List (b, us) |> mk) in
          List (b, ife :: rest) |> mk
        (* else begin
          (** A trivial-IF is [IF _ THEN TRUE ELSE _] or [IF _ THEN FALSE ELSE _]
                           or [IF _ THEN _ ELSE TRUE] or [IF _ THEN _ ELSE FALSE]
            This code obtains one trivial-IF, and pull it out of the List.
          *)
(* iter (fun e -> Util.eprintf " --> @[<hov>%a@]" (Expr.Fmt.pp_print_expr (snd scx, Ctx.dot)) e) ifs; *)
            let exists_trivial es = List.exists (fun e -> is_true e || is_false e) es in
(* (if List.exists (fun e -> let _,(t,u) = split_if e in exists_trivial [t;u]) ifs then
  (Util.eprintf "    [second case]" ;
  Util.eprintf "LIST-IF: %a" (Expr.Fmt.pp_print_expr (snd scx, Ctx.dot)) (List (b,ifs) %% []);
  Util.eprintf "LIST-re: %a" (Expr.Fmt.pp_print_expr (snd scx, Ctx.dot)) (List (b,rest) %% []))
  else ()); *)
            let rec get_trivial_if r = function
              | [] -> None, r
              | (c,(t,u)) :: ifs ->
                  if exists_trivial [t;u] then Some (c,t,u), r @ ifs
                  else get_trivial_if (r @ [c,(t,u)]) ifs
            in
            let io, ifs = get_trivial_if [] (map split_if ifs) in
            let es = (map (fun (c,(t,u)) -> ifte c t u) ifs) @ rest in
            match io with
            | Some (c,t,u) ->
                let u = (List (b, u :: es) |> mk) |> self#expr scx in
                let t = (List (b, t :: es) |> mk) |> self#expr scx in
                ifte c u t |> self#expr scx
            | None ->
                List (b, es) |> mk
          end *)
        else List (b, es) |> mk
      end else
        List (b, es) |> mk

    | Choose (v, None, ex) ->
      let scx' = adj scx (Fresh (v, Shape_expr, Constant, Unbounded) @@ v) in
      let ex = self#expr scx' ex in
      let choose = From_hint.make_choose v ex in
      choose.core |> mk

    | Choose (v, Some dom, ex) ->
      (** Note: Don't attach types to h or ix1. They will be later substituted
           by other expressions with (maybe) other types.  *)
      let ex = conj (mem ix1 (sh1 dom)) ex in
      let choose = From_hint.make_choose v ex in
      choose.core
      |> mk
      |> self#expr scx

    (* | Internal B.BOOLEAN -> SetEnum [tla_true ; tla_false] |> mk *)

    | _ ->
      super#expr scx e
  end
