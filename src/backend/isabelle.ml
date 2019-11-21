(*
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** This file contains functions to handle isabelle theories, which
    are used in two ways:
    1. to use Isabelle as a back-end to prove obligations
    2. to use Isabelle to check proofs output by TLAPM and Zenon.
*)

Revision.f "$Rev$";;

open Ext
open Property

open Format
open Fmtutil
open Tla_parser

open Expr.T
open Expr.Subst
open Proof.T

module B = Builtin

type ctx = int Ctx.ctx
let dot : ctx = Ctx.dot
let bump : ctx -> ctx = Ctx.bump
let length : ctx -> int = Ctx.length



let cook x = "is" ^ pickle x

let adj cx v =
  let cx = Ctx.push cx (pickle v.core) in
  (cx, Ctx.string_of_ident (fst (Ctx.top cx)))

let rec adjs cx = function
  | [] -> (cx, [])
  | v :: vs ->
      let (cx, v) = adj cx v in
      let (cx, vs) = adjs cx vs in
      (cx, v :: vs)

let lookup_id cx n =
  assert (n > 0 && n <= Ctx.length cx) ;
  let id = Ctx.string_of_ident (fst (Ctx.index cx n)) in
  id

let crypthash (cx : ctx) e =
  let s =
    let b = Buffer.create 10 in
    let fmt = Format.formatter_of_buffer b in
    Expr.Fmt.pp_print_expr (Deque.empty, cx) fmt e ;
    Format.pp_print_flush fmt () ;
    Buffer.contents b
  in
  "hash'" ^ Digest.to_hex (Digest.string s)

let print_shape ff shp =
  match shp with
  | Shape_expr -> fprintf ff "c";
  | Shape_op (n) ->
     for _i = 1 to n do fprintf ff "c => "; done;
     fprintf ff "c";
;;

exception Unsupported of string;;

let rec pp_apply sd cx ff op args = match op.core with
  | Ix n ->
     let id = lookup_id cx n in
     begin match args with
     | [] -> fprintf ff "%s" id
     | _ ->
        fprintf ff "(%s (%a))" id
                (pp_print_delimited (pp_print_expr sd cx)) args
     end
  | Opaque id ->
     begin match args with
     | [] -> fprintf ff "(%s :: c)" (pickle id)
     | _ ->
        fprintf ff "(%s (%a) :: c)" (pickle id)
                (pp_print_delimited (pp_print_expr sd cx)) args
     end
  | Internal b -> begin
      let atomic op =
        fprintf ff "%s" op
      and unary op e =
        fprintf ff "(%s %a)"
          op
          (pp_print_expr sd cx) e
      and binary op e f =
        fprintf ff "(%a %s %a)"
          (pp_print_expr sd cx) e
          op
          (pp_print_expr sd cx) f
      and nonfix op args =
        fprintf ff "(%s (%a))"
          op
          (pp_print_delimited (pp_print_expr sd cx)) args
      in
      match b, args with
        | B.TRUE, [] -> atomic "TRUE"
        | B.FALSE, [] -> atomic "FALSE"
        | B.Implies, [e ; f] -> binary "\\<Rightarrow>" e f
        | B.Equiv, [e ; f] -> binary "\\<Leftrightarrow>" e f
        | B.Conj, [e ; f] -> binary "\\<and>" e f
        | B.Disj, [e ; f] -> binary "\\<or>" e f
        | B.Neg, [e] -> unary "~" e
        | B.Eq, [e ; f] -> binary "=" e f
        | B.Neq, [e ; f] -> binary "\\<noteq>" e f

        | B.STRING, [] -> atomic "STRING"
        | B.BOOLEAN, [] -> atomic "BOOLEAN"
        | B.SUBSET, [e] -> unary "SUBSET" e
        | B.UNION, [e] -> unary "UNION" e
        | B.DOMAIN, [e] -> unary "DOMAIN" e
        | B.Subseteq, [e ; f] -> binary "\\<subseteq>" e f
        | B.Mem, [e ; f] -> binary "\\<in>" e f
        | B.Notmem, [e ; f] -> binary "\\<notin>" e f
        | B.Setminus, [e ; f] -> binary "\\\\" e f
        | B.Cap, [e ; f] -> binary "\\<inter>" e f
        | B.Cup, [e ; f] -> binary "\\<union>" e f
        | (B.Prime | B.StrongPrime), [e] -> assert false
         (* prime handling was moved from the backends and TLAPM to action frontends *)
         (*  begin match e.core  with
             | Apply(op,args) ->
                if (List.fold_left (fun a b -> a && Expr.Constness.is_const b)
                                   true args)
                then nonfix (crypthash cx op) args
                else atomic (crypthash cx e)
             | _ ->  atomic (crypthash cx e)
           end *)
        | B.Leadsto, [e; f] -> raise (Unsupported "Leadsto")
        | B.ENABLED, _ -> raise (Unsupported "ENABLED")
        | B.UNCHANGED, [e] -> assert false
            (* UNCHANGED is now handled by the action front-end *)
            (* pp_print_expr sd cx ff
              (Apply (Internal B.Eq @@ e,
                      [ Apply (Internal B.StrongPrime @@ e, [e]) @@ e ; e ]) @@
                      e) *)
        | B.Cdot, [e ; f] ->
            binary (cook "\\cdot") e f
        | B.Actplus, [e ; f] ->
            binary (cook "-+->") e f
        | B.Box _, [e] -> raise (Unsupported "Box")
        | B.Diamond, [e] -> raise (Unsupported "Diamond")
        | B.Nat, [] -> atomic "Nat"
        | B.Int, [] -> atomic "Int"
        | B.Real, [] -> atomic (cook "Real")
        | B.Plus, [e ; f] -> nonfix "arith_add" [e ; f]
        | B.Minus, [e ; f] -> nonfix "arith_add" [e ; Apply (Internal B.Uminus @@ f, [f]) @@ f]
        | B.Uminus, [e] -> nonfix "minus" [e]
        | B.Times, [e ; f] -> nonfix "mult" [e ; f]
        | B.Ratio, [e ; f] -> nonfix (cook "/") [e ; f]
        | B.Quotient, [e ; f] -> nonfix (cook "\\div") [e ; f]
        | B.Remainder, [e ; f] -> nonfix (cook "%") [e ; f]
        | B.Exp, [e ; f] -> nonfix (cook "^") [e ; f]
        | B.Infinity, [] -> atomic (cook "Infinity")
        | B.Lteq, [e ; f] -> nonfix "leq" [e ; f]
        | B.Lt, [e ; f] -> nonfix "less" [e ; f]
        | B.Gteq, [e ; f] -> nonfix "geq" [e ; f]
        | B.Gt, [e ; f] -> nonfix "greater" [e ; f]
        | B.Range, [e ; f] -> nonfix (cook "..") [e ; f]

        | B.Seq, [e] -> nonfix "Seq" [e]
        | B.Len, [e] -> nonfix "Len" [e]
        | B.BSeq, [e] -> nonfix "BSeq" [e]
        | B.Cat, [e ; f] -> nonfix (cook "\\circ") [e ; f]
        | B.Append, [e ; f] -> nonfix "Append" [e ; f]
        | B.Head, [e] -> nonfix "Head" [e]
        | B.Tail, [e] -> nonfix "Tail" [e]
        | B.SubSeq, [e ; m ; n] -> nonfix "SubSeq" [e ; m ; n]
        | B.SelectSeq, [e ; f] -> nonfix "SelectSeq" [e ; f]

        | B.OneArg, [e ; f] -> binary ":>" e f
        | B.Extend, [e ; f] -> binary "@@" e f
        | B.Print, [e ; v] -> nonfix "Print" [e ; v]
        | B.PrintT, [e] -> nonfix "PrintT" [e]
        | B.Assert, [e ; o] -> nonfix "Assert" [e ; o]
        | B.JavaTime, [] -> nonfix "JavaTime" []
        | B.TLCGet, [i] -> nonfix "TLCGet" [i]
        | B.TLCSet, [i ; v] -> nonfix "TLCSet" [i ; v]
        | B.Permutations, [s] -> nonfix "Permutations" [s]
        | B.SortSeq, [s ; o] -> nonfix "SortSeq" [s ; o]
        | B.RandomElement, [s] -> nonfix "RandomElement" [s]
        | B.Any, [] -> atomic "Any"
        | B.ToString, [v] -> nonfix "ToString" [v]

        | B.Unprimable, [e] ->
            pp_print_expr sd cx ff e
        | B.Irregular, [e] ->
            atomic (crypthash cx e)
        | _ ->
            Util.eprintf ~at:op "arity mismatch@\n%a"
                         (Expr.Fmt.pp_print_expr (Deque.empty, cx))
                         (Tuple (op :: args) @@ op) ;
            failwith "Backend.Isabelle.pp_apply"
    end
  | Lambda (vs, e) ->
     let rec spin l cx =
       match l with
       | [] -> fprintf ff ". %a" (pp_print_expr sd cx) e;
       | (v, _) :: vs ->
          let (ecx, v) = adj cx v in
          fprintf ff "%s " v;
          spin vs ecx;
     in
     fprintf ff "\\<lambda> ";
     spin vs cx;
  | _ -> assert false

and fmt_expr sd cx e = match e.core with
  | ( Ix _ | Internal _ | Opaque _ | Lambda _ ) ->
      Fu.Atm (fun ff -> pp_apply sd cx ff e [])
  | Apply (op, args) ->
      Fu.Atm (fun ff -> pp_apply sd cx ff op args)
  | Bang _ ->
      failwith "Backend.Isabelle.module"
  | Sequent sq ->
      Fu.Big (fun ff -> ignore (pp_print_sequent sd cx ff sq))
  | With (e, _) ->
      fmt_expr sd cx e
  | Let _ -> raise (Unsupported "LET")
  | List (Refs, []) ->
      fmt_expr sd cx (Internal Builtin.TRUE @@ e)
  | List (Refs, [e]) ->
      fmt_expr sd cx e
  | List (q, es) ->
      let rep = match q with
        | And | Refs -> "& "
        | Or -> "| "
      in
      Fu.Big (fun ff ->
                fprintf ff "%a"
                  (pp_print_delimited
                     ~sep:(fun ff () ->
                             pp_print_space ff () ;
                             pp_print_string ff rep)
                     (pp_print_expr sd cx)) es)
  | If (e, f, g) ->
      Fu.Big (fun ff ->
                fprintf ff "cond(%a, %a, %a)"
                  (pp_print_expr sd cx) e
                  (pp_print_expr sd cx) f
                  (pp_print_expr sd cx) g)
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
      let rep = match q with
        | Forall -> ("\\<forall>", "=>")
        | Exists -> ("\\<exists>", "&")
      in begin
        match b with
          | (v, _, No_domain) ->
              let (ecx, v) = adj cx v in
              Fu.Big (fun ff ->
                        fprintf ff "%s%s : %a"
                          (fst rep) v (pp_print_expr sd ecx) e)
          | (v, _, Domain d) ->
              let (ecx, v) = adj cx v in
              Fu.Big (fun ff ->
                        fprintf ff
                          "%s %s \\<in> %a : %a"
                          (fst rep)
                          v
                          (pp_print_expr sd cx) d
                          (pp_print_expr sd ecx) e)
          | _ ->
              assert false
      end
  | Tquant (q, vs, e) ->
      let rep = match q with
        | Forall -> "\\\\AA"
        | Exists -> "\\\\EE"
      in
      raise (Unsupported rep)

  | Choose (v, None, e) ->
      let (ecx, v) = adj cx v in
      Fu.Big begin fun ff ->
        fprintf ff
          "Choice(%%%s. %a)"
          v (pp_print_expr sd ecx) e
      end
  | Choose (v, Some dom, e) ->
      let (ecx, v) = adj cx v in
      Fu.Big begin fun ff ->
        fprintf ff
          "bChoice(%a, %%%s. %a)"
          (pp_print_expr sd cx) dom
          v (pp_print_expr sd ecx) e
      end
  | SetSt (v, dom, e) ->
      let (ecx, v) = adj cx v in
      Fu.Atm (fun ff ->
                fprintf ff "subsetOf(%a, %%%s. %a)"
                  (pp_print_expr sd cx) dom
                  v (pp_print_expr sd ecx) e)
  | SetOf (e, [(_, _, Domain dom) as b]) ->
      let (ecx, (v, _, _)) = extend_bound cx b in
      Fu.Atm (fun ff ->
                fprintf ff "setOfAll(%a, %%%s. %a)"
                  (pp_print_expr sd cx) dom
                  v (pp_print_expr sd ecx) e)
  | SetOf (_, _ :: _) -> raise (Unsupported "SetOf (tuple)")
  | SetOf _ -> assert false
  | SetEnum es ->
      Fu.Atm (fun ff ->
                fprintf ff "{%a}"
                  (pp_print_delimited (pp_print_expr sd cx)) es)
  | Fcn ([b], e) ->
      let (ecx, b) = extend_bound cx b in
      Fu.Atm (fun ff ->
                fprintf ff "[%a %s %a]"
                  (pp_print_bound sd cx) b "\\<mapsto>"
                  (pp_print_expr sd ecx) e)
  | Fcn _ -> raise (Unsupported "function (tuple)")
  | FcnApp (f, [e]) ->
      Fu.Atm begin
        fun ff ->
          fprintf ff "fapply (%a, %a)"
            (pp_print_expr sd cx) f
            (pp_print_expr sd cx) e
      end
  | FcnApp (f, es) ->
      Fu.Atm begin
        fun ff ->
          fprintf ff "fapply (%a, <<%a>>)"
            (pp_print_expr sd cx) f
            (pp_print_delimited (pp_print_expr sd cx)) es
      end
  | Arrow (a, b) ->
      Fu.Big (fun ff ->
                (* fprintf ff "FuncSet(%a, %a)" *)
                fprintf ff "[%a %s %a]"
                  (pp_print_expr sd cx) a
                  "\\<rightarrow>"
                  (pp_print_expr sd cx) b)
  | Rect fs ->
      Fu.Atm (fun ff ->
                fprintf ff "[%a]"
                  (pp_print_delimited
                     (fun ff (v, e) ->
                        fprintf ff "''%s'' : %a" v (pp_print_expr sd cx) e)) fs)
  | Record fs ->
      Fu.Atm (fun ff ->
                fprintf ff "(%a)"
                  (pp_print_delimited
                     ~sep:(fun ff () -> pp_print_string ff " @@ ")
                     (fun ff (v, e) ->
                        fprintf ff "(''%s'' :> %a)" v (pp_print_expr sd cx) e))
                  fs)
  | Except (e, xs) ->
      Fu.Atm (fun ff ->
                fprintf ff "[%a EXCEPT %a]"
                  (pp_print_expr sd cx) e
                  (pp_print_delimited
                     (fun ff (tr, e) ->
                        fprintf ff "!%a = %a"
                          (pp_print_delimited ~sep:(fun ff () -> ())
                             (fun ff -> function
                                | Except_dot s -> fprintf ff "[''%s'']" s
                                | Except_apply e -> fprintf ff "[%a]" (pp_print_expr sd cx) e))
                          tr
                          (pp_print_expr sd cx)
                          e))
                  xs)
  | Dot (re, f) ->
      fmt_expr sd cx (FcnApp (re, [String f @@ e]) @@ e)
  | Tuple es ->
      Fu.Atm (fun ff ->
                fprintf ff "<<%a>>"
                  (pp_print_delimited (pp_print_expr sd cx)) es)
  | Product [e ; f] ->
      Fu.Atm (fun ff ->
                fprintf ff "(%a \\<times> %a)"
                  (pp_print_expr sd cx) e
                  (pp_print_expr sd cx) f)
  | Product es ->
      Fu.Big (fun ff ->
                fprintf ff "Product(\\<langle>%a\\<rangle>)"
                  (pp_print_delimited (pp_print_expr sd cx)) es)
  | Sub (q, e, f) ->
      Fu.Big (fun ff ->
                fprintf ff "%s(%a,%a)"
                  (match q with Box -> cook "a'box'sub" | _ -> "a'dia'sub")
                  (pp_print_expr sd cx) e
                  (pp_print_expr sd cx) f)
  | Tsub (q, e, f) ->
      Fu.Big (fun ff ->
                fprintf ff "%s(%a,%a)"
                  (match q with Box -> cook "a'box'tsub" | _ -> "a'dia'tsub")
                  (pp_print_expr sd cx) e
                  (pp_print_expr sd cx) f)
  | Fair (q, e, f) ->
      Fu.Big (fun ff ->
                fprintf ff "%s(%a,%a)"
                  (match q with Weak -> cook "a'wf" | _ -> cook "a'sf")
                  (pp_print_expr sd cx) e
                  (pp_print_expr sd cx) f)
  | Case (arms, None) ->
      Fu.Big begin fun ff ->
        let (ps, es) = List.split arms in
        fprintf ff "Case(<<%a>>,<<%a>>)"
          (pp_print_delimited (pp_print_expr sd cx)) ps
          (pp_print_delimited (pp_print_expr sd cx)) es
      end
  | Case (arms, Some oth) ->
      Fu.Big begin fun ff ->
        let (ps, es) = List.split arms in
        fprintf ff "CaseOther(<<%a>>,<<%a>>,%a)"
          (pp_print_delimited (pp_print_expr sd cx)) ps
          (pp_print_delimited (pp_print_expr sd cx)) es
          (pp_print_expr sd cx) oth
      end
  | String s ->
      Fu.Atm (fun ff -> fprintf ff "''%s''" s)
  | Num (m, "") ->
      let rec uloop = function
        | 0 -> "0"
        | n -> "Succ[" ^ uloop (n - 1) ^ "]"
      in
      Fu.Atm (fun ff -> fprintf ff "(%s)" (uloop (int_of_string m)))
  | Num (m, n) -> raise (Unsupported "real constants")
  | At _ ->
      Errors.bug ~at:e "Backend.Isabelle: @"
  | Parens (e, _) ->
      fmt_expr sd cx e

and extend_bound cx (v, kn, dom) =
  let (cx, v) = adj cx v in
  (cx, (v, kn, dom))

and pp_print_bound sd cx ff (v, _, dom) = match dom with
  | No_domain ->
      pp_print_string ff v
  | Domain dom ->
      fprintf ff " %s \\<in> %a "
        v (pp_print_expr sd cx) dom
  | Ditto -> assert false

and pp_print_expr sd cx ff e =
  let parens = match sd, e.core with
    | true, Sequent _ -> false
    | _ -> true
  in
  pp_open_hbox ff () ;
  if parens then pp_print_string ff "(" ;
  Fu.pp_print_minimal ff (fmt_expr sd cx e) ;
  if parens then pp_print_string ff ")" ;
  pp_close_box ff ()

and pp_print_sequent sd =
  if sd then begin
    fun cx ff sq ->
      pp_open_vbox ff 0 ;
      let ret = pp_print_sequent_outer cx ff sq in
      pp_close_box ff () ;
      ret
  end else pp_print_sequent_inner

and pp_print_sequent_outer cx ff sq = match Deque.front sq.context with
  | None ->
      fprintf ff "shows \"%a\"" (pp_print_expr false cx) sq.active ;
      cx
  | Some (h, hs) -> begin
      match h.core with
        | Flex nm ->
            let (ncx, nm) = adj cx nm in
            fprintf ff "fixes %s %s'@,"
              nm nm ;
            pp_print_sequent_outer ncx ff { sq with context = hs }
        | Fresh (nm, _, _, Bounded (b, Visible)) ->
            let (ncx, nm) = adj cx nm in
            fprintf ff "fixes %s@,assumes %s_in : @[<h>\"(%s \\<in> %a)\"@]@,"
              nm nm nm (pp_print_expr false cx) b ;
            pp_print_sequent_outer ncx ff { sq with context = hs }
        | Fresh (nm, _, _, _) ->
            let (ncx, nm) = adj cx nm in
            fprintf ff "fixes %s@," nm ;
            pp_print_sequent_outer ncx ff { sq with context = hs }
        | Fact (e, Visible, _) ->
            let ncx = Ctx.bump cx in
            begin try
              let null = make_formatter (fun _ _ _ -> ()) (fun () -> ()) in
              pp_print_expr false cx null e;  (* may raise Unsupported *)
              fprintf ff "assumes v'%d: \"%a\"@,"
                (Ctx.length cx) (pp_print_expr false cx) e
            with Unsupported msg ->
              fprintf ff "(* omitted temporal assumption : %s *)@," msg
            end;
            pp_print_sequent_outer ncx ff { sq with context = hs }
        | Fact (_, _, _) ->
            let ncx = Ctx.bump cx in
            pp_print_sequent_outer ncx ff { sq with context = hs }
        | Defn ({ core = Operator (nm, _) | Instance (nm, _)
                         | Recursive (nm, _) },
                _, _, _) ->
            let ncx = fst (adj cx nm) in
            fprintf ff "(* usable definition %s suppressed *)@," nm.core ;
            pp_print_sequent_outer ncx ff { sq with context = hs }
              (*
               * | _ ->
               *     failwith "Backend.Isabelle.pp_print_sequent"
               *)
        |  Defn ({ core = Bpragma _ } , _, _, _) -> cx
    end

and pp_print_sequent_inner cx ff sq = match Deque.front sq.context with
  | None ->
      pp_print_expr false cx ff sq.active ;
      cx
  | Some (h, hs) -> begin
      match h.core with
        | Flex nm ->
            let (ncx, nm) = adj cx nm in
            fprintf ff "(\\<And> %s %s'." nm nm ;
            let ret = pp_print_sequent_inner ncx ff { sq with context = hs } in
            fprintf ff ")" ;
            ret
        | Fresh (nm, _, _, Bounded (b, Visible)) ->
            let (ncx, nm) = adj cx nm in
              fprintf ff "(\\<And> %s :: c. %s \\<in> %a \\<Longrightarrow> "
                 nm nm (pp_print_expr false cx) b;
            let ret = pp_print_sequent_inner ncx ff { sq with context = hs } in
            fprintf ff ")" ;
            ret
        | Fresh (nm, shp, _, _) ->
            let (ncx, nm) = adj cx nm in
            fprintf ff "(\\<And> %s :: %a. " nm print_shape shp;
            let ret = pp_print_sequent_inner ncx ff { sq with context = hs } in
            fprintf ff ")" ;
            ret
        | Fact (e, Visible, _) ->
            let ncx = Ctx.bump cx in
              fprintf ff "(%a \\<Longrightarrow> " (pp_print_expr false cx) e ;
              (* OLD fprintf ff "(%a \\<Rightarrow> " (pp_print_expr false cx) e ; *)
            let ret = pp_print_sequent_inner ncx ff { sq with context = hs } in
            fprintf ff ")" ;
            ret
        | Fact (_, _, _) ->
            let ncx = Ctx.bump cx in
            pp_print_sequent_inner ncx ff { sq with context = hs }
        | Defn (df, _, _, _) -> raise (Unsupported "Inner definition")
    end

type obx = obligation * string list * int * int

let thy_header ?(verbose=true) modname oc =
  Printf.fprintf oc "(* automatically generated -- do not edit manually *)\n";
  Printf.fprintf oc "theory %s imports Constant Zenon begin\n" modname;
  if verbose then
    Printf.fprintf oc
                   "ML_command {* writeln (\"*** TLAPS PARSED\\n\"); *}\n";
  let tdoms_table = [
    cook "Real"     , 0, None;
    cook "/"        , 2, None;
    cook "\\div"    , 2, None;
    cook "%"        , 2, None;
    cook ".."       , 2, None;
    cook "Infinity" , 0, None;
    cook "[]"       , 1, None;
    cook "<>"       , 1, None;
  ] in
  let ax_table = [] in
  Printf.fprintf oc "consts\n";
  let f (p, arity, _) =
    Printf.fprintf oc "  \"%s\" :: " p;
    if arity > 0 then begin
      Printf.fprintf oc "\"[c";
      for i = 2 to arity do Printf.fprintf oc ",c" done;
      Printf.fprintf oc "] => c\"\n";
    end else
      Printf.fprintf oc "c\n";
  in
  List.iter f tdoms_table;
  if ax_table <> [] then begin
    Printf.fprintf oc "\naxioms\n" ;
    List.iter begin
      fun (axname, cookie, axbod) -> match cookie with
        | None -> Printf.fprintf oc "  %s : \"%s\"\n" axname axbod
        | Some cookie ->
            Printf.fprintf oc "  %s [%s] : \"%s\"\n" axname cookie axbod
    end ax_table;
  end;
  Printf.fprintf oc "\n";
;;

let thy_init modname thy =
  begin try Sys.remove thy with _ -> () end ;
  if !Params.verbose then Util.printf "(* removing %S *)" thy;
  let thyout = open_out thy in
  thy_header modname thyout;
  thyout
;;

let thy_write thyout ob proof =
  let obid = Option.get ob.id in
  try
    let sq = Sequent ob.obl.core @@ nowhere in
    (* Expr.Fmt.pp_print_expr (Deque.empty, Ctx.dot) err_formatter sq ; *)
    ignore (flush_str_formatter ());
    pp_print_expr true Ctx.dot str_formatter (sq);
    let statement = flush_str_formatter () in
    Printf.fprintf thyout "lemma ob'%d:\n" obid;
    Printf.fprintf thyout "%s" statement;
    Printf.fprintf thyout "(is \"PROP ?ob'%d\")\n" obid;
    Printf.fprintf thyout "proof -\n";
    Printf.fprintf thyout "ML_command {* writeln \"*** TLAPS ENTER %d\"; *}\n"
                   obid;
    Printf.fprintf thyout "show \"PROP ?ob'%d\"\n" obid;
    Printf.fprintf thyout "%s" proof;
    Printf.fprintf thyout
                   "ML_command {* writeln \"*** TLAPS EXIT %d\"; *} qed\n"
                   obid;
  with Failure msg ->
    Errors.warn "Proof of obligation %d cannot be checked:\n%s\n" obid msg;
;;

let thy_close thy thyout =
  Printf.fprintf thyout "end\n";
  close_out thyout;
  Util.printf "(* created new %S *)" thy;
;;

(* Make theory file for proving (isabelle as normal back-end). *)
(* FIXME get rid of the buffer and write directly to the file *)
let thy_temp ob tac tempname thyout =
  thy_header ~verbose:false tempname thyout;
  let obid = Option.get ob.id in
  let obfp = Option.default "no fingerprint" ob.fingerprint in
  Printf.fprintf thyout "lemma ob'%d: (* %s *)\n" obid obfp;
  let ff = Format.formatter_of_out_channel thyout in
  begin try
    pp_print_expr true Ctx.dot ff (Sequent ob.obl.core @@ nowhere);
  with Unsupported msg ->
    failwith ("isabelle : unsupported operator " ^ msg)
  end;
  Format.pp_print_flush ff ();
  Printf.fprintf thyout "(is \"PROP ?ob'%d\")\n" obid;
  Printf.fprintf thyout "proof -\n";
  Printf.fprintf thyout "show \"PROP ?ob'%d\"\n" obid;
  Printf.fprintf thyout "using assms by %s\n" tac;
  Printf.fprintf thyout "qed\n";
  Printf.fprintf thyout "end\n";
;;

let success_banner modname nmiss =
  let allobs =
    Printf.sprintf "Exported obligations in module %S verified" modname
  in
  let maxlen = String.length allobs in
  let banner_top = "/-" ^ String.make maxlen '-' ^ "-\\" in
  let banner_bot = "\\-" ^ String.make maxlen '-' ^ "-/" in
  Util.printf "\n  %-*s" maxlen banner_top ;
  Util.printf "  | %-*s |" maxlen allobs ;
  Util.printf "  %-*s" maxlen banner_bot ;
  if nmiss <> 0 then begin
    Util.printf ">>> Reminder: there %s %d missing (sub)proof%s in module %S."
                (if nmiss = 1 then "was" else "were") nmiss
                (if nmiss = 1 then "" else "s") modname;
    Util.printf ">>> Rerun tlapm with the --summary flag for details."
  end
;;

let parsed_re = Str.regexp "^ *\\*\\*\\* TLAPS PARSED"
let enter_re = Str.regexp "\\*\\*\\* TLAPS ENTER \\([0-9]+\\)"
let exit_re = Str.regexp "\\*\\*\\* TLAPS EXIT \\([0-9]+\\)"
let failure_location_re = Str.regexp "^ *\\*\\*\\*.*(line \\([0-9]+\\) of"

type isa_msg = Input of string | Output of string

module IntSet = Set.Make (struct type t = int let compare = (-) end);;

let find_obid linenum thy =
  let ic = open_in thy in
  let curobl = ref "0" in
  let rec spin n =
    let l = input_line ic in
    begin try
      ignore (Str.search_forward enter_re l 0);
      curobl := Str.matched_group 1 l;
    with Not_found -> ()
    end;
    begin try
      ignore (Str.search_forward exit_re l 0);
      curobl := "0";
    with Not_found -> ()
    end;
    if n < linenum then spin (n+1)
  in
  spin 1;
  match int_of_string !curobl with
  | 0 -> None
  | x -> Some x
;;

(* Check the [thy] file with Isabelle and report any problems. *)
let recheck (modname, nmiss, thy) =
  Errors.err "Checking the proofs with Isabelle. This may take a long time.";
  let teardown = ref [] in
  let isa_mod = Filename.chop_suffix thy ".thy" in
  let isacmd = Params.solve_cmd Params.isabelle isa_mod in
  let logfile = Filename.concat !Params.output_dir "isabelle.log" in
  let log =
    try
      let logout = open_out_bin logfile in
      teardown := (fun () -> close_out logout) :: !teardown ;
      if !Params.verbose then
        Util.printf "(* Isabelle interaction log in %S *)" logfile;
      Printf.fprintf logout "%% %s\n%!" isacmd;
      function
      | Input msg ->
         Printf.fprintf logout "[sent] %s\n%!" msg
      | Output msg ->
         Printf.fprintf logout "%s\n%!" msg
    with _ -> (fun _ -> ())
  in
  let (pid, iout) = System.launch_process isacmd in
  let failure_line = ref (-1) in
  let inprog = ref IntSet.empty in
  let finished = ref IntSet.empty in
  let report (errfn : (_, _, _, _, _, _) format6 -> _) msg =
    if IntSet.cardinal !inprog > 0 && !failure_line <= 0 then begin
      let f x accu = (Printf.sprintf "%d" x) :: accu in
      let obls = IntSet.fold f !inprog [] in
      errfn "%s" (String.concat " " (msg :: obls));
    end
  in
  Util.printf ~nonl:() "(* Isabelle parsing %S ...%!" thy;
  let linepos = ref 3 in
  let fds = ref [Unix.stdin; iout] in
  let tb_buf = System.make_line_buffer Unix.stdin in
  let isa_buf = System.make_line_buffer iout in
  let stopped = ref false in
  let do_isa_line line =
    log (Output line);
    begin try
      ignore (Str.search_forward parsed_re line 0) ;
      Util.printf " done *)";
      Util.printf "(* Obligation checking trace follows. *)";
      Util.printf ~nonl:() "(* %!";
    with Not_found -> ()
    end;
    begin try
      ignore (Str.search_forward failure_location_re line 0);
      if !failure_line <= 0 then
        failure_line := int_of_string (Str.matched_group 1 line)
    with Not_found -> ()
    end;
    begin try
      ignore (Str.search_forward enter_re line 0);
      let obstr = Str.matched_group 1 line in
      let obid = int_of_string obstr in
      inprog := IntSet.add obid !inprog;
      Util.printf ~nonl:() "+%s %!" obstr;
      linepos := 2 + String.length obstr + !linepos;
    with Not_found -> ()
    end;
    begin try
      ignore (Str.search_forward exit_re line 0);
      let obstr = Str.matched_group 1 line in
      let obid = int_of_string obstr in
      inprog := IntSet.remove obid !inprog;
      finished := IntSet.add obid !finished ;
      Util.printf ~nonl:() "-%s %!" obstr;
      linepos := 2 + String.length obstr + !linepos;
    with Not_found -> ()
    end;
    if !linepos >= 70 then begin
      Util.printf ~nonl:() "*)\n(* %!";
      linepos := 3;
    end;
  in
  let do_toolbox_command cmd =
    match cmd with
    | System.Eof -> fds := [iout];
    | System.Killall ->
       System.kill_tree pid;
       stopped := true;
       raise Exit;
    | _ -> ()
  in
  begin try while true do
    let (ready, _, _) = Unix.select !fds [] [] 3600. in
    if List.mem Unix.stdin ready then
      List.iter do_toolbox_command (System.read_toolbox_commands tb_buf)
    else if List.mem iout ready then begin
      let f l =
        match l with
        | System.Leof -> raise Exit;
        | System.Line l -> do_isa_line l
      in
      List.iter f (System.read_lines isa_buf)
    end
  done with Exit -> ()
  end;
  Util.printf "*)" ;
  if !stopped then begin
    Errors.warn "Proof checking was cancelled by the user.";
    report Errors.warn "... while these obligations were being checked:\n";
  end else begin
    report Errors.err "Unexpected error while checking these obligations:\n";
    if !failure_line > 0 then begin
      match find_obid !failure_line thy with
      | None -> Errors.err "Unexpected error while checking proofs.";
      | Some obid ->
         Errors.err "Isabelle/TLA+ rejected the proof of obligation %d.\n\
                     See %S for details." obid logfile;
    end else begin
      Errors.err "Proof checking done. No errors found.";
    end;
    let (_, status) = Unix.waitpid [] pid in
    if status <> Unix.WEXITED 0 then
      Errors.warn "Warning: Isabelle/TLA+ returned non-zero exit code";
    List.iter (fun fn -> fn ()) !teardown;
    if !failure_line = 0 then success_banner modname nmiss;
  end;
;;
