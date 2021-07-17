(* Interface to Zenon.

Copyright (C) 2008-2010  INRIA and Microsoft Corporation
*)

(** Zenon backend *)

open Ext
open Format
open Fmtutil
open Tla_parser
open Property

open Expr.T
open Expr.Subst
open Proof.T

module B = Builtin

include (Isabelle : sig
           type ctx
           val dot : ctx
           val bump : ctx -> ctx
           val length : ctx -> int
           val adj : ctx -> Util.hint -> ctx * string
           val cook : string -> string
           val lookup_id : ctx -> int -> string
           val crypthash : ctx -> expr -> string
           val extend_bound:
              ctx -> bound ->
              ctx * (string * Expr.T.kind * Expr.T.bound_domain)
         end)

exception Unsupported of string
let unsupp o = raise (Unsupported o)
let failwith_unsupp op = failwith ("Unsupported operator `" ^ op ^ "`.\n")

let rec pp_apply sd cx ff op args = match op.core with
  | Ix n ->
     let id = lookup_id cx n in
     begin match args with
     | [] ->
        pp_print_string ff id
     | _ ->
        fprintf ff "(%s %a)" id
                (pp_print_delimited ~sep:pp_print_space (pp_print_expr sd cx))
                args
     end
  | Opaque id -> begin
     match args with
     | [] ->
        pp_print_string ff (pickle id)
     | _ ->
        fprintf ff "(%s %a)" (pickle id)
                (pp_print_delimited ~sep:pp_print_space (pp_print_expr sd cx))
                args
     end
  | Internal b -> begin
      let atomic op =
        pp_print_string ff op
      and nonatomic op args =
        fprintf ff "(%s %a)"
          op
          (pp_print_delimited ~sep:pp_print_space (pp_print_expr sd cx)) args
      and negate doit =
        pp_print_string ff "(-. " ;
        doit () ;
        pp_print_string ff ")"
      in match b, args with
      (* Logic operators *)
      | B.TRUE, [] -> atomic "T."
      | B.FALSE, [] -> atomic "F."
      | B.Implies, [e ; f] -> nonatomic "=>" [e ; f]
      | B.Equiv, [e ; f] -> nonatomic "<=>" [e ; f]
      | B.Conj, [e ; f] -> nonatomic "/\\" [e ; f]
      | B.Disj, [e ; f] -> nonatomic "\\/" [e ; f]
      | B.Neg, [e] -> nonatomic "-." [e]
      | B.Eq, [e ; f] -> nonatomic "=" [e ; f]
      | B.Neq, [e ; f] -> negate (fun () -> nonatomic "=" [e ; f])
      (* Function operators *)
      | B.DOMAIN, [e] -> nonatomic "TLA.DOMAIN" [e]
      (* Set operators *)
      | B.STRING, [] -> atomic "TLA.STRING"
      | B.BOOLEAN, [] -> atomic "(TLA.set T. F.)"  (* abbrev *)
      (* Set theory operators *)
      | B.SUBSET, [e] -> nonatomic "TLA.SUBSET" [e]
      | B.UNION, [e] -> nonatomic "TLA.UNION" [e]
      | B.Subseteq, [e ; f] -> nonatomic "TLA.subseteq" [e ; f]
      | B.Mem, [e ; f] -> nonatomic "TLA.in" [e ; f]
      | B.Notmem, [e ; f] -> negate (fun () -> nonatomic "TLA.in" [e ; f])
      | B.Setminus, [e ; f] -> nonatomic "TLA.setminus" [e ; f]
      | B.Cap, [e ; f] -> nonatomic "TLA.cap" [e ; f]
      | B.Cup, [e ; f] -> nonatomic "TLA.cup" [e ; f]
      (* Modal operators *)
      | (B.Prime | B.StrongPrime), [e] -> assert false
         (* prime handling was moved from the backends and TLAPM to action frontends *)
         (* begin match e.core  with
            | Apply(op,args) -> begin if (List.fold_left (fun a b -> a && b) true (List.map Expr.Constness.is_const args))
                                      then nonatomic (crypthash cx op) args
                                      else  atomic (crypthash cx e) end
            | _ ->  atomic (crypthash cx e)
          end*)
      | B.Leadsto, [e ; f] ->
            failwith_unsupp "Leadsto"
            (* unsupp "Leadsto" *)
      | B.ENABLED, [e] ->
            failwith_unsupp "ENABLED"
            (* unsupp "ENABLED" *)
            (* nonatomic (cook "ENABLED") [e] *)
      | B.UNCHANGED, [e] -> assert false
          (* UNCHANGED handling was moved to the front-end *)
          (*pp_print_expr sd cx ff
            (Apply (Internal B.Eq @@ e,
                    [ Apply (Internal B.StrongPrime @@ e, [e]) @@ e ; e ]) @@ e)
           *)
      | B.Cdot, [e ; f] ->
            failwith_unsupp "\\cdot"
            (* unsupp "\\cdot" *)
            (* nonatomic (cook "\\cdot") [e ; f] *)
      | B.Actplus, [e ; f] ->
            failwith_unsupp "-+->"
            (* unsupp "-+->" *)
            (* nonatomic (cook "-+->") [e ; f] *)
      | B.Box _, [e] ->
            failwith_unsupp "[]"
            (* unsupp "[]" *)
      | B.Diamond, [e] ->
            failwith_unsupp "<>"
            (* unsupp "<>" *)
      (* Arithmetic operators *)
      | B.Nat, [] -> atomic "arith.N"
      | B.Int, [] -> atomic "arith.Z"
      | B.Real, [] -> atomic "arith.R"
      | B.Plus, [e ; f] -> nonatomic "arith.add" [e ; f]
      | B.Minus, [e ; f] ->
          nonatomic "arith.add"
            [e ; Apply (Internal B.Uminus @@ f, [f]) @@ f]
      | B.Uminus, [e] -> nonatomic "arith.minus" [e]
      | B.Times, [e ; f] -> nonatomic "arith.mul" [e ; f]
      | B.Ratio, [e ; f] -> nonatomic "arith.div" [e ; f]
      | B.Quotient, [e ; f] -> nonatomic "arith.euclidiv" [e ; f]
      | B.Remainder, [e ; f] -> nonatomic "arith.mod" [e ; f]
      | B.Exp, [e ; f] -> nonatomic "arith.power" [e ; f]
      | B.Infinity, [] -> atomic "arith.Infinity"
      | B.Lteq, [e ; f] -> nonatomic "arith.le" [e ; f]
      | B.Lt, [e ; f] -> nonatomic "arith.lt" [e ; f]
      | B.Gteq, [e ; f] -> nonatomic "arith.le" [f ; e]  (* abbrev *)
      | B.Gt, [e ; f] -> nonatomic "arith.lt" [f ; e]    (* abbrev *)
      | B.Range, [e ; f] -> nonatomic "arith.intrange" [e ; f]
      (* Sequence operators *)
      | B.Seq, [e] -> nonatomic "TLA.Seq" [e]
      | B.Len, [e] -> nonatomic "TLA.Len" [e]
      | B.BSeq, [e] -> nonatomic "TLA.BSeq" [e]
      | B.Cat, [e ; f] -> nonatomic "TLA.concat" [e ; f]
      | B.Append, [e ; f] -> nonatomic "TLA.Append" [e ; f]
      | B.Head, [e] -> nonatomic "TLA.Head" [e]
      | B.Tail, [e] -> nonatomic "TLA.Tail" [e]
      | B.SubSeq, [e ; m ; n] -> nonatomic "TLA.SubSeq" [e ; m ; n]
      | B.SelectSeq, [e ; f] -> nonatomic "TLA.SelectSeq" [e ; f]
      (* TLC operators *)
      | B.OneArg, [e ; f] -> nonatomic "TLA.oneArg" [e ; f]
      | B.Extend, [e ; f] -> nonatomic "TLA.extend" [e ; f]
      | B.Print, [e ; v] -> nonatomic "TLA.Print" [e ; v]
      | B.PrintT, [e] -> nonatomic "TLA.PrintT" [e]
      | B.Assert, [e ; o] -> nonatomic "TLA.Assert" [e ; o]
      | B.JavaTime, [] -> nonatomic "TLA.JavaTime" []
      | B.TLCGet, [i] -> nonatomic "TLA.TLCGet" [i]
      | B.TLCSet, [i ; v] -> nonatomic "TLA.TLCSet" [i ; v]
      | B.Permutations, [s] -> nonatomic "TLA.Permutations" [s]
      | B.SortSeq, [s ; o] -> nonatomic "TLA.SortSeq" [s ; o]
      | B.RandomElement, [s] -> nonatomic "TLA.RandomElement" [s]
      | B.Any, [] -> atomic "TLA.Any"
      | B.ToString, [v] -> nonatomic "TLA.ToString" [v]
      (* Internal operators *)
      | B.Unprimable, [e] -> pp_print_expr sd cx ff e
      | B.Irregular,[e] -> atomic (crypthash cx e)

      | _ ->
          Errors.set op "zenon.ml: Arity mismatch";
          Util.eprintf ~at:op "Arity mismatch" ;
          failwith "Backend.Zenon.fmt_apply"
    end
  | Lambda (vs, e) ->
     let rec spin l cx =
       match l with
       | [] -> fprintf ff ") %a)" (pp_print_expr sd cx) e;
       | (v, _) :: vs ->
          let (ecx, v) = adj cx v in
          fprintf ff "%s " v;
          spin vs ecx;
     in
     fprintf ff "((";
     spin vs cx;
  | _ -> assert false

and fmt_expr sd cx e =
  match e.core with
    | ( Ix _ | Internal _ | Opaque _ | Lambda _ ) ->
        Fu.Atm (fun ff -> pp_apply sd cx ff e [])
    | Apply (op, args) ->
        Fu.Atm (fun ff -> pp_apply sd cx ff op args)
    | Bang _ ->
        Errors.bug ~at:e "Backend.Zenon.fmt_exp: !"
    | Sequent sq when sd ->
        Fu.Big (fun ff -> pp_print_sequent cx ff sq)
    | Sequent sq -> begin
        match Deque.front sq.context with
          | None -> fmt_expr sd cx sq.active
          | Some ({core = Fact (e, Visible, _)}, hs) ->
              let ncx = bump cx in
              Fu.Big (fun ff ->
                        fprintf ff "(=> %a %a)" (pp_print_expr sd cx) e
                          (pp_print_expr sd ncx) (Sequent { sq with context = hs } @@ e))
          | Some ({core = Flex nm}, hs) ->
              let (ncx, nm) = adj cx nm in
              Fu.Big (fun ff ->
                        fprintf ff "(A. ((%s) (A. ((%s') %a))))" nm nm
                          (pp_print_expr sd ncx) (Sequent { sq with context = hs } @@ e))
          | Some ({core = Fresh (nm, _, _, Bounded (b, Visible))}, hs) ->
              let (ncx, nm) = adj cx nm in
              Fu.Big begin
                fun ff ->
                  fprintf ff
                    "(TLA.bAll %a ((%s) %a))"
                    (pp_print_expr sd cx) b
                    nm
                    (pp_print_expr sd ncx) (Sequent { sq with context = hs } @@ e)
              end
          | Some ({core = Fresh (nm, _, _, _)}, hs) ->
              let (ncx, nm) = adj cx nm in
              Fu.Big (fun ff ->
                        fprintf ff "(A. ((%s) %a))" nm
                          (pp_print_expr sd ncx) (Sequent { sq with context = hs } @@ e))
          | Some ({core = Fact (_, Hidden, _)}, hs) ->
              let ncx = bump cx in
              fmt_expr sd ncx (Sequent { sq with context = hs } @@ e)
          | _ ->
             Errors.bug ~at:e "Backend.Zenon.fmt_exp: internal error (sequent)"
      end
    | With (e, _) ->
        fmt_expr sd cx e
    | Let (ds, f) ->
        Errors.bug ~at:e "Backend.Zenon.fmt_exp: encountered LET" ;
    | If (e, f, g) ->
        Fu.Big (fun ff ->
                  fprintf ff "(TLA.cond %a %a %a)"
                    (pp_print_expr sd cx) e
                    (pp_print_expr sd cx) f
                    (pp_print_expr sd cx) g)
    | List (Refs, []) ->
             Errors.bug ~at:e "Backend.Zenon.fmt_exp: internal error (List)"
        (* fmt_expr sd cx (Internal Builtin.TRUE @@ e) *)
    | List (Refs, [e]) ->
        fmt_expr sd cx e
    | List (q, es) ->
        let rep = match q with
          | And | Refs -> "/\\"
          | Or -> "\\/"
        in
        Fu.Big begin
          fun ff -> fprintf ff "(%s %a)" rep
            (pp_print_delimited ~sep:pp_print_space (pp_print_expr sd cx)) es
        end
    | Quant (q, [], e) ->
        fmt_expr sd cx e
    | Quant (q, (_, _, bdom as b) :: bs, e) ->
        let e = match bs with
          | [] -> e
          | (v, k, Ditto) :: bs ->
              let (_, bs) = app_bounds (shift 1) ((v, k, bdom) :: bs) in
              Quant (q, bs, e) @@ e
          | bs ->
              let (_, bs) = app_bounds (shift 1) bs in
              Quant (q, bs, e) @@ e
        in
        let (rep, brep) =
          match q with
            | Forall -> ("A.", "TLA.bAll")
            | Exists -> ("E.", "TLA.bEx")
        in begin
          match b with
            | (v, _, No_domain) ->
                let (ecx, v) = adj cx v in
                Fu.Big (fun ff ->
                          fprintf ff "(%s ((%s) %a))"
                            rep v (pp_print_expr sd ecx) e)
            | (v, _, Domain b) ->
                let (ecx, v) = adj cx v in
                Fu.Big begin
                  fun ff ->
                    fprintf ff
                      "(%s %a ((%s) %a))"
                      brep
                      (pp_print_expr sd cx) b
                      v (pp_print_expr sd ecx) e
                end
            | _ -> assert false
        end
    | Tquant _ -> unsupp "\\AA or \\EE"
    | Choose (v, None, e) ->
        let (ecx, v) = adj cx v in
        Fu.Big begin fun ff ->
          fprintf ff
            "(t. ((%s) %a))" v (pp_print_expr sd ecx) e
        end
    | Choose (v, Some ran, e) ->
        let (ecx, v) = adj cx v in
        Fu.Big begin fun ff ->
          fprintf ff
            "(TLA.bChoice %a ((%s) %a))"
            (pp_print_expr sd cx) ran
            v (pp_print_expr sd ecx) e
        end
    | SetSt (v, ran, e) ->
        let (ecx, v) = adj cx v in
        Fu.Atm begin
          fun ff ->
            fprintf ff "(TLA.subsetOf %a ((%s) %a))"
              (pp_print_expr sd cx) ran
              v (pp_print_expr sd ecx) e
        end
    | SetOf (e, [b]) ->
        let (ecx, b) = extend_bound cx b in
        Fu.Atm (fun ff ->
                  fprintf ff "(TLA.setOfAll %a ((%a) %a))"
                    (pp_print_boundset sd cx) (b @@ e)
                    (pp_print_boundvar cx) b
                    (pp_print_expr sd ecx) e)
    | SetOf _ ->
        unsupp "Setof (multiple declared constants)"
    | SetEnum [] -> Fu.Atm (fun ff -> fprintf ff "TLA.emptyset")
    | SetEnum es ->
        Fu.Big (fun ff ->
                  fprintf ff "(TLA.set";
                  List.iter (fun x -> fprintf ff " %a" (pp_print_expr sd cx) x) es;
                  fprintf ff ")";
               )
    | Fcn ([b], e) ->
        let (ecx, b) = extend_bound cx b in
        Fu.Atm (fun ff ->
                  fprintf ff "(TLA.Fcn %a ((%a) %a))"
                    (pp_print_boundset sd cx) (b @@ e)
                    (pp_print_boundvar cx) b
                    (pp_print_expr sd ecx) e)
    | Fcn _ ->
        unsupp "Fcn (multiple declared constants)"
    | FcnApp (f, [e]) ->
        Fu.Atm begin
          fun ff ->
            fprintf ff "(TLA.fapply %a %a)"
              (pp_print_expr sd cx) f
              (pp_print_expr sd cx) e
        end
    | FcnApp (f, es) ->
        Fu.Atm begin
          fun ff ->
            fprintf ff "(TLA.fapply %a (TLA.tuple %a))"
              (pp_print_expr sd cx) f
              (pp_print_delimited ~sep:pp_print_space (pp_print_expr sd cx)) es
        end
    | Arrow (a, b) ->
        Fu.Atm (fun ff ->
                  fprintf ff "(TLA.FuncSet %a %a)"
                    (pp_print_expr sd cx) a
                    (pp_print_expr sd cx) b)
    | Rect rs ->
        Fu.Atm begin fun ff ->
          let print_pair (f, v) =
            fprintf ff " %a %a" (pp_print_expr sd cx) (String f @@ e)
                                (pp_print_expr sd cx) v
          in
          fprintf ff "(TLA.recordset";
          List.iter print_pair rs;
          fprintf ff ")"
        end
    | Record rs ->
        Fu.Atm begin fun ff ->
          let print_pair (f, v) =
            fprintf ff " %a %a" (pp_print_expr sd cx) (String f @@ e)
                                (pp_print_expr sd cx) v
          in
          fprintf ff "(TLA.record";
          List.iter print_pair rs;
          fprintf ff ")"
        end
    | Except (e, [([Except_apply e1], e2)]) ->
        Fu.Atm (fun ff ->
                  fprintf ff "(TLA.except %a %a %a)"
                    (pp_print_expr sd cx) e (pp_print_expr sd cx) e1 (pp_print_expr sd cx) e2
               )
    | Except (e1, [([Except_dot f], e2)]) ->
        fmt_expr sd cx (Except (e1, [([Except_apply (String f @@ e)], e2)]) @@ e)
    | Except _ -> unsupp "complex EXCEPT"
    | Dot (re, f) ->
        fmt_expr sd cx (FcnApp (re, [String f @@ e]) @@ e)
    | Tuple es ->
        Fu.Atm (fun ff -> fprintf ff "(TLA.tuple %a)"
                  (pp_print_delimited ~sep:pp_print_space
                     (pp_print_expr sd cx))
                  es)
    | Product [e ; f] ->
        Fu.Atm begin
          fun ff ->
            fprintf ff "(TLA.prod %a %a)"
              (pp_print_expr sd cx) e
              (pp_print_expr sd cx) f
        end
    | Product es ->
        Fu.Atm (fun ff ->
                  fprintf ff "(TLA.Product (TLA.tuple %a))"
                    (pp_print_delimited ~sep:pp_print_space (pp_print_expr sd cx)) es)
    | Sub (q, e, f) -> unsupp "Sub"
    | Tsub (q, e, f) -> unsupp "Tsub"
    | Fair (q, e, f) -> unsupp "Fair"

    | Expr.T.Case (arms, oth) ->
        let pp_case ff (e1, e2) =
          fprintf ff "%a %a" (pp_print_expr sd cx) e1 (pp_print_expr sd cx) e2
        in
        Fu.Big (fun ff ->
                  fprintf ff "(TLA.CASE %a "
                    (pp_print_delimited ~sep:pp_print_space pp_case) arms;
                  match oth with
                    | None -> fprintf ff ")"
                    | Some e -> fprintf ff "%a)@]" (pp_print_expr sd cx) e
               )
    | String s ->
        Fu.Atm (fun ff -> fprintf ff "\"%s\"" s)
    | Num (m, "") ->
        let rec uloop = function
          | 0 -> "0"
          | n -> "(TLA.fapply TLA.Succ " ^ uloop (n - 1) ^ ")"
        in
        Fu.Atm (fun ff -> fprintf ff "%s" (uloop (int_of_string m)))
    | Num _ -> unsupp "Real number constants"
    | At _ ->
        Errors.bug ~at:e "Backend.Zenon.fmt_exp: encountered @"
    | Parens (e, _) ->
        fmt_expr sd cx e
    | QuantTuply _
    | ChooseTuply _
    | SetStTuply _
    | SetOfTuply _
    | FcnTuply _ -> assert false

and pp_print_boundvar cx ff (v, _, _) = pp_print_string ff v

and pp_print_boundset sd cx ff b = match b.core with
  | (_, _, Domain e) ->
      pp_print_expr sd cx ff e
  | _ ->
      Errors.bug ~at:b "Backend.Zenon.pp_print_boundset: Fcn or SetSt without bounds"

and pp_print_expr sd cx ff e =
  Fu.pp_print_minimal ff (fmt_expr sd cx e)

(* Print a sequent as a zenon input file: list of assumptions followed
   by the goal.
   [cx] is the context
   [ff] is the Format buffer
   [sq] is the sequent
*)
and pp_print_sequent cx ff sq =
  match Deque.front sq.context with
  | None ->
     fprintf ff "$goal %a" (pp_print_expr false cx) sq.active;
  | Some ({core = Fresh (nm, _, _, Bounded (b, Visible))}, hs) ->
     let (ncx, nm) = adj cx nm in
     fprintf ff "$hyp \"%s_in\" (TLA.in %s %a)@\n" nm nm
             (pp_print_expr false cx) b;
     pp_print_sequent ncx ff {sq with context = hs}
  | Some ({core = Fresh (nm, _, _, _)}, hs)
  | Some ({core = Flex nm}, hs) ->
     let (ncx, nm) = adj cx nm in
     pp_print_sequent ncx ff { sq with context = hs }
  | Some ({core = Defn ({core = Operator (nm, _)}, _, h, _)}, hs)
  | Some ({core = Defn ({core = Instance (nm, _)}, _, h, _)}, hs)
  | Some ({core = Defn ({core = Recursive (nm, _)}, _, h, _)}, hs)
  | Some ({core = Defn ({core = Bpragma (nm, _, _)}, _, h, _)}, hs) ->
     let (ncx, nm) = adj cx nm in
     if h = Visible then fprintf ff "; usable definition %s suppressed@." nm;
     pp_print_sequent ncx ff {sq with context = hs}
  | Some ({core = Fact (e, Visible, _)}, hs) ->
     let ncx = bump cx in
     begin try
       let null = make_formatter (fun _ _ _ -> ()) (fun () -> ()) in
       pp_print_expr false cx null e; (* may raise Unsupported *)
       fprintf ff "$hyp \"v'%d\" %a@\n" (length cx) (pp_print_expr false cx) e;
     with Unsupported msg ->
       fprintf ff "; omitted temporal assumption : %s @." msg;
     end;
     pp_print_sequent ncx ff {sq with context = hs}
  | Some ({core = Fact (_, Hidden, _)}, hs) ->
     let ncx = bump cx in
     pp_print_sequent ncx ff {sq with context = hs}
  | Some ({core=FreshTuply _}, _) ->
      assert false  (* unexpected case *)


let pp_print_obligation ff ob =
  fprintf ff ";; obligation #%d@\n" (Option.get ob.id);
  try
    pp_print_sequent dot ff ob.obl.core;
  with Unsupported msg ->
    failwith ("Zenon: unsupported operator " ^ msg)
