(*
 * backend/ls4.ml --- LS4 interaction
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** LS4 backend *)

Revision.f "$Rev: 32466 $";;

open Ext
open Format
open Fmtutil
open Tla_parser
open Property

open Expr.T
open Expr.Subst
open Proof.T

module B = Builtin

(* Function added by Damien to remain compatible with OCaml 3.12, which
   does not have the [trim] function.
   Note: I think this function is in fact useless.
*)
let is_only_whitespace s =
  let check c =
    match c with
    | ' ' | '\t' | '\012' | '\r' | '\n' -> ()
    | _ -> raise Exit
  in
  try String.iter check s; true
  with Exit -> false
;;

(*
let rec pp_apply sd cx ff op args = match op.core with
  | Ix n ->
      let id = lookup_id cx n in
      pp_apply sd cx ff { op with core = Opaque id } args
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
      and unsupp o =
        Errors.warning := true;
        Errors.set op ("TLAPM does not handle "^o);
        Util.eprintf ~at:op "%s not supported" o ;
        failwith "Backend.Zenon.pp_apply"
      in match b, args with
      | B.TRUE, [] -> atomic "T."
      | B.FALSE, [] -> atomic "F."
      | B.Implies, [e ; f] -> nonatomic "=>" [e ; f]
      | B.Equiv, [e ; f] -> nonatomic "<=>" [e ; f]
      | B.Conj, [e ; f] -> nonatomic "/\\" [e ; f]
      | B.Disj, [e ; f] -> nonatomic "\\/" [e ; f]
      | B.Neg, [e] -> nonatomic "-." [e]
      | B.Eq, [e ; f] -> nonatomic "=" [e ; f]
      | B.Neq, [e ; f] -> negate (fun () -> nonatomic "=" [e ; f])

      | B.STRING, [] -> atomic "TLA.STRING"
      | B.BOOLEAN, [] -> atomic "(TLA.set T. F.)"  (* abbrev *)
      | B.SUBSET, [e] -> nonatomic "TLA.SUBSET" [e]
      | B.UNION, [e] -> nonatomic "TLA.UNION" [e]
      | B.DOMAIN, [e] -> nonatomic "TLA.DOMAIN" [e]
      | B.Subseteq, [e ; f] -> nonatomic "TLA.subseteq" [e ; f]
      | B.Mem, [e ; f] -> nonatomic "TLA.in" [e ; f]
      | B.Notmem, [e ; f] -> negate (fun () -> nonatomic "TLA.in" [e ; f])
      | B.Setminus, [e ; f] -> nonatomic "TLA.setminus" [e ; f]
      | B.Cap, [e ; f] -> nonatomic "TLA.cap" [e ; f]
      | B.Cup, [e ; f] -> nonatomic "TLA.cup" [e ; f]
      | (B.Prime | B.StrongPrime), [e] -> begin
           Errors.warning := true;
           Errors.set op ("zenon does not handle action reasoning - make sure to use a frontend that deals with actions");
           failwith "action reasoning in backend zenon"
         end
         (* prime handling was moved from the backends and TLAPM to action frontends *)
         (* begin match e.core  with
            | Apply(op,args) -> begin if (List.fold_left (fun a b -> a && b) true (List.map Expr.Constness.is_const args))
                                      then nonatomic (crypthash cx op) args
                                      else  atomic (crypthash cx e) end
            | _ ->  atomic (crypthash cx e)
          end*)

      | B.Leadsto, [e ; f] -> begin
           Errors.warning := true;
           Errors.set op ("TLAPM does not handle yet temporal logic");
           failwith "temporal logic"
         end
      | B.ENABLED, [e] -> unsupp "ENABLED"
      | B.UNCHANGED, [e] ->
           Errors.warn ~at:op "zenon does not handle action reasoning - make sure to use a frontend that deals with actions";
           failwith "Backend.Zenon: UNCHANGED";
          (*pp_print_expr sd cx ff
            (Apply (Internal B.Eq @@ e,
                    [ Apply (Internal B.StrongPrime @@ e, [e]) @@ e ; e ]) @@ e)
*)
      | B.Cdot, [e ; f] -> nonatomic (cook "\\cdot") [e ; f]
      | B.Actplus, [e ; f] -> nonatomic (cook "-+->") [e ; f]
      | B.Box _, [e] -> begin Errors.warning := true; Errors.set op ("TLAPM does not handle yet temporal logic");failwith "temporal logic" end (*nonatomic "TLA.box" [e]*)
      | B.Diamond, [e] -> begin Errors.warning := true; Errors.set op ("TLAPM does not handle yet temporal logic");failwith "temporal logic" end (*nonatomic (cook "<>") [e]*)

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

      | B.Seq, [e] -> nonatomic "TLA.Seq" [e]
      | B.Len, [e] -> nonatomic "TLA.Len" [e]
      | B.BSeq, [e] -> nonatomic "TLA.BSeq" [e]
      | B.Cat, [e ; f] -> nonatomic "TLA.concat" [e ; f]
      | B.Append, [e ; f] -> nonatomic "TLA.Append" [e ; f]
      | B.Head, [e] -> nonatomic "TLA.Head" [e]
      | B.Tail, [e] -> nonatomic "TLA.Tail" [e]
      | B.SubSeq, [e ; m ; n] -> nonatomic "TLA.SubSeq" [e ; m ; n]
      | B.SelectSeq, [e ; f] -> nonatomic "TLA.SelectSeq" [e ; f]

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
        fmt_expr sd cx (Internal Builtin.TRUE @@ e)
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
    | Tquant _ ->
        Errors.warning := true;
        Errors.set e "TLAPM does not handle yet temporal quantifiers";
        Util.eprintf ~at:e "cannot handle temporal quantifiers" ;
        failwith "Backend.Zenon.fmt_expr"
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
        Errors.warning := true;
        Errors.set e "TLAPM does not handle multiple bounds in set-of construct";
        Util.eprintf ~at:e "cannot handle multiple bounds in set-of construct" ;
        failwith "Backend.Zenon.fmt_expr"
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
        Errors.warning := true;
        Errors.set e "TLAPM does not handle functions of more than one argument";
        Util.eprintf ~at:e "functions of more than one argument not supported" ;
        failwith "Backend.Zenon.fmt_expr"
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
    | Except _ ->
        Errors.warning := true;
        Errors.set e "TLAPM does not handle complex EXCEPT";
        Util.eprintf ~at:e "cannot handle complex EXCEPT" ;
        failwith "Backend.Zenon.fmt_expr"
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
    | Sub (q, e, f) ->
        Fu.Atm (fun ff ->
                  fprintf ff "(%s %a %a)"
                    (match q with
                       | Box -> cook "a'box'sub"
                       | _ -> cook "a'dia'sub")
                    (pp_print_expr sd cx) e
                    (pp_print_expr sd cx) f)
    | Tsub (q, e, f) ->
        (*Errors.set e "TLAPM does not handle yet temporal logic";
        Util.eprintf ~at:e "cannot handle temporal logic" ;
        failwith "Zenon.temporal"*)
          Fu.Atm (fun ff ->
                  fprintf ff "(%s %a %a)"
                    (match q with
                       | Box -> cook "a'box'tsub"
                       | _ -> cook "a'dia'tsub")
                    (pp_print_expr sd cx) e
                    (pp_print_expr sd cx) f)

    | Fair (q, e, f) ->
        Fu.Big (fun ff ->
                  fprintf ff "(%s %a %a)"
                    (match q with
                       | Weak -> cook "a'wf"
                       | _ -> cook "a'sf")
                    (pp_print_expr sd cx) e
                    (pp_print_expr sd cx) f)

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
    | Num _ ->
        Errors.warning := true;
        Errors.set e "TLAPM does not handle yet real numbers";
        Util.eprintf ~at:e "cannot handle real numbers" ;
        failwith "Backend.Zenon.fmt_expr"
    | At _ ->
        Errors.bug ~at:e "Backend.Zenon.fmt_exp: encountered @"
    | Parens (e, _) ->
        fmt_expr sd cx e
*)

let visitor = object (self : 'self)
  inherit [Format.formatter] Expr.Visit.iter as super
  method print scx ff e = self#expr (ff, scx) e
  method p_binary (ff,scx) op f1 f2 = fprintf ff "(%a %s %a)" (self#print scx) f1 op
    (self#print scx) f2
  method p_unary (ff,scx) op f = fprintf ff "(%s %a)" op
    (self#print scx) f
  method p_atom ff at = fprintf ff "%s" at
  method myhyp ((ff,scx) as scxp) h is_first =
      let ret = match h.core with
      (* antecedents serve both as holders of facts and as containers of the
       * values of the de-bruijn indicies. we want to print only facts but must
       * add other formulas into the indices deque *)
        | Fresh _
        | Flex _
        | Defn _
        | Fact (_, Hidden, _) ->
            false
        | Fact (e, Visible, _) ->
            fprintf ff  "%s" (if (not is_first) then " & " else "");
            self#expr scxp e;
            true
      in
      (ret, Expr.Visit.adj scxp h)
  method myhyps ((ff,scx) as scxp) hs had_first = match Deque.front hs with
      | None -> scxp
      | Some (h, hs) when (Deque.null hs) ->
          let (_, scxp) = self#myhyp scxp h (not had_first) in
          scxp
      | Some (h, hs) ->
          let (ret, scxp) = self#myhyp scxp h (not had_first) in
          let had_first = (ret || had_first) in
          let scxp = self#myhyps scxp hs had_first in
          scxp
  method expr ((ff,scx) as scxp) e = 
    match e.core with
      (* treating infix binary pltl operators *)
    | Apply ({core = Internal B.Implies}, [f1;f2]) -> self#p_binary scxp "->" f1 f2
    | Apply ({core = Internal B.Equiv}, [f1;f2]) -> self#p_binary scxp "<->" f1 f2
    | Apply ({core = Internal B.Conj}, [f1;f2]) -> self#p_binary scxp "&" f1 f2
    | Apply ({core = Internal B.Disj}, [f1;f2]) -> self#p_binary scxp "|" f1 f2
    (* atoms *)
    | Ix n ->
        if n > Deque.size scx then
          Errors.bug ~at:e "Ls4.visitor#expr: unknown bound variable"
        else begin match Deque.nth ~backwards:true scx (n - 1) with
          | None -> failwith "impossible"
          | Some({core = Fresh (name, _, _, _) | Flex name}) ->
              self#expr scxp { e with core = Opaque name.core }
          | _ -> super#expr scxp e
        end
    | Opaque id -> self#p_atom ff id
    (* nullary builtins *)
    | Internal B.TRUE ->  self#p_atom ff "(cc | ~ cc)"
    | Internal B.FALSE -> self#p_atom ff "(cc & ~ cc)"
    (* unary builtins *)
    | Apply ({core = Internal B.Box _}, [f]) -> self#p_unary scxp "always" f
    | Apply ({core = Internal B.Diamond}, [f]) -> self#p_unary scxp "sometime" f
    | Apply ({core = Internal B.Prime}, [f]) -> self#p_unary scxp "next" f
    | Apply ({core = Internal B.Neg}, [f]) -> self#p_unary scxp "~" f
    (* the main sequent *)
    | Sequent sq ->
        let buf = Buffer.create 4096 in
        let formatter = Format.formatter_of_buffer buf in
        let (_,scx) = self#myhyps (formatter,scx) sq.context false in
        let () = pp_print_flush formatter () in
        let str = Buffer.contents buf in
        if is_only_whitespace str then self#expr scxp sq.active
        else  begin
          fprintf ff "(";
          fprintf ff "%s" str;
          fprintf ff " -> ";
          self#expr (ff,scx) sq.active;
          fprintf ff ")"
        end
    | List (Refs, []) ->
        self#expr scxp (Internal Builtin.TRUE @@ e)
    | List (Refs, [e]) ->
        self#expr scxp e
    | List (q, es) ->
        let rep = match q with
        | And | Refs -> " & "
        | Or -> " | "
        in
	self#write_list scxp rep es
    (* first-order failures including remaining applications *)
    | _ -> fprintf err_formatter " failure: fol - %a" (Expr.Fmt.pp_print_expr
      (scx, Ctx.dot)) e; super#expr scxp e
  (* failwith "Ls4.pp_print_obligation: first order constructs are not
     * allowed. Please use a PLTL frontend" *)
    method write_list ((ff,scx) as scxp) rep = function
      | [] -> Errors.bug "Backend.LS4: internal error (List)"
      | [e] -> self#expr scxp e
      | e::es ->
        fprintf ff "("; self#expr scxp e; fprintf ff "%s" rep;
        self#write_list scxp rep es; fprintf ff ")"
end

let pp_print_obligation ff ob =
  (* we negate the query as we try to refute it *)
  fprintf ff "not (%a)"
  (visitor#print Deque.empty)  (noprops (Sequent ob.obl.core))
;;
