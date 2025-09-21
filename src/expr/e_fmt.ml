(* Formatting of expressions.

Copyright (C) 2008-2010  INRIA and Microsoft Corporation
*)

(* START dflags
 *
 *      "alldefs"    show all definitions
 *      "hidden"     show all assumptions (subsumes above)
 *
 * END dflags *)

(* FIXME remove all non-ASCII characters from this source file *)

open Ext
open Property

open E_t
open Format
open Fmtutil
module Fu = Tla_parser.Fu


type ctx = hyp Deque.dq * int Ctx.ctx

let is_letter c =
  match c with
  | 'A'..'Z' | 'a'..'z' -> true
  | _ -> false


let pp_print_var ff v = pp_print_string ff v.core

let bump (hx, vx) = (hx, Ctx.bump vx)

let adj (hx, vx) v =
  let vx = Ctx.push vx v.core in
  ((hx, vx), Ctx.string_of_ident (Ctx.front vx))

let rec adjs cx = function
  | [] -> (cx, [])
  | v :: vs ->
      let (cx, v) = adj cx v in
      let (cx, vs) = adjs cx vs in
      (cx, v :: vs)

let extend_bound ?(prevdom=None) cx (v, _, dom) =
  let (ecx, v) = adj cx v in
  let dom = match dom with
    | Ditto -> prevdom
    | No_domain -> None
    | Domain d -> Some d
  in
  (ecx, (v, dom))

let rec extend_bounds ?(prevdom=None) cx = function
  | [] -> (cx, [])
  | b :: bs ->
      let (cx, b) = extend_bound ~prevdom:prevdom cx b in
      let (cx, bs) = extend_bounds ~prevdom:(snd b) cx bs in
      (cx, b :: bs)

let is_hidden h = match h.core with
  | Defn (_, _, us, _)
  | Fact (_, us,_) -> us = Hidden
  | _ -> false

let rec is_with e = match e.core with
  | Lambda (_, e) -> is_with e
  | Sequent sq -> is_with sq.active
  | With _ -> true
  | _ -> false

let has_with df = match df.core with
  | Operator (_, e) -> is_with e
  | _ -> false

let elide h =
  not (Params.debugging "hidden")
  && begin
    match h.core with
      | Defn (df, wd, us, _) ->
          not (Params.debugging "alldefs")
          && (us = Hidden || has_with df || wd <> User)
      | Fact (e, us,_) ->
          us = Hidden || is_with e
      | _ -> false
  end

let rec fmt_expr ?(temp=false) cx ew = match ew.core with
  | ( Ix _ | Opaque _ | Internal _ ) ->
      fmt_apply cx ew []
  | Lambda (vss, e) ->
      Fu.Big (fun ff -> pp_print_lambda cx ff vss e)
  | Bang (e, sels) ->
      Fu.Atm begin
        fun ff ->
          pp_print_expr ~temp:temp cx ff e ;
          pp_print_sels cx ff sels
      end
  | Apply (op, args) ->
      fmt_apply cx op args
  | Sequent sq ->
      Fu.Big (fun ff -> ignore (pp_print_sequent ~temp:temp cx ff sq))
  | With (e, m) ->
      if Params.debugging "meth" then
        Fu.Atm begin fun ff ->
          fprintf ff "@[<hov2>(%a (* : %a *))@]"
            (pp_print_expr ~temp:temp cx) e
            Method.pp_print_method m
        end
      else fmt_expr ~temp:temp cx e
  | If (e, f, g) ->
      Fu.Big begin
        fun ff ->
          fprintf ff "@[<hv2>@[<b2>IF@ %a@]@ @[<b2>THEN %a@]@ @[<b2>ELSE %a@]@]"
            (pp_print_expr ~temp:temp cx) e
            (pp_print_expr ~temp:temp cx) f
            (pp_print_expr ~temp:temp cx) g
      end
  | List (Refs, []) ->
      Fu.Atm (fun ff -> pp_print_string ff "TRUE")
  | List (Refs, [e]) ->
      fmt_expr ~temp:temp cx e
  | List (q, es) ->
      let qrep = match q with
        | And | Refs -> "/\\"
        | _   -> "\\/" in
      let pp_print_elem ff e =
        fprintf ff "@[<h>%s %a@]" qrep (pp_print_expr ~temp:temp cx) e
      in
      Fu.Big begin
        fun ff ->
          fprintf ff "@[<v0>%a@]"
            (pp_print_delimited ~sep:pp_print_cut pp_print_elem) es
      end
  | Let (ds, e) ->
      Fu.Big (fun ff ->
                fprintf ff "@[<hv0>LET @[<v0>" ;
                let cx = pp_print_defns cx ff ds in
                fprintf ff "@]@\nIN  %a@]" (pp_print_expr ~temp:temp cx) e)
  | Quant (q, bs, e) ->
      let (ecx, bsf) = fmt_bounds cx bs in
      let rep = match q with
        | Forall -> "\\A"
        | Exists -> "\\E"
      in
      Fu.Big (fun ff ->
                fprintf ff "@[<b3>%s @[<b0>%t@] :@ %a@]"
                  rep bsf (pp_print_expr ~temp:temp ecx) e)

  | Tquant (q, vs, e) ->
      let (ecx, vs) = adjs cx vs in
      let rep = match q with
        | Forall -> "\\AA"
        | Exists -> "\\EE"
      in
      Fu.Big (fun ff ->
                fprintf ff "@[<b4>%s @[<b0>%a@] : %a@]"
                  rep
                  (pp_print_delimited pp_print_string) vs
                  (pp_print_expr ~temp:temp ecx) e)
  | Choose (v, optdom, e) ->
      let (ecx, v) = adj cx v in
      begin match optdom with
        | Some dom ->
            Fu.Big begin fun ff ->
              fprintf ff "@[<b2>CHOOSE @[<b2>%s \\in@ %a@] :@ %a@]"
                v (pp_print_expr ~temp:temp cx) dom
                (pp_print_expr ~temp:temp ecx) e
            end
        | None ->
            Fu.Big begin fun ff ->
              fprintf ff "@[<b2>CHOOSE %s :@ %a@]"
                v (pp_print_expr ~temp:temp ecx) e
            end
      end
  | SetSt (v, dom, e) ->
      let (ecx, v) = adj cx v in
      Fu.Atm (fun ff ->
                fprintf ff "@[<b3>{@[<b2>%s \\in@ %a@] :@ %a}@]"
                  v (pp_print_expr ~temp:temp cx) dom
                  (pp_print_expr ~temp:temp ecx) e)
  | SetOf (e, bs) ->
      let (ecx, bsf) = fmt_bounds cx bs in
      Fu.Atm (fun ff ->
                fprintf ff "@[<b3>{%a :@ %t}@]"
                  (pp_print_expr ~temp:temp ecx) e bsf)
  | SetEnum es ->
      Fu.Atm begin
        fun ff ->
          fprintf ff "@[<h>{@[<b0>%a@]}@]"
            (pp_print_delimited (pp_print_expr ~temp:temp cx)) es
      end
  | Arrow (e, f) ->
      Fu.Atm begin
        fun ff ->
          fprintf ff "@[<b3>[%a ->@ %a]@]"
            (pp_print_expr ~temp:temp cx) e
            (pp_print_expr ~temp:temp cx) f
      end
  | Fcn (bs, e) ->
      let (ecx, bsf) = fmt_bounds cx bs in
      Fu.Atm (fun ff ->
                fprintf ff "@[<b3>[%t |->@ %a]@]"
                  bsf (pp_print_expr ~temp:temp ecx) e)
  | FcnApp (f, es) ->
      let e = fmt_expr ~temp cx f in
      let (lpar, rpar) =
        match e with
        | Fu.Atm _ -> "", ""
        | _ -> "(", ")"
      in
      Fu.Atm begin
        fun ff ->
          fprintf ff "@[<h>%s%a%s@[<b1>[%a]@]@]"
            lpar
            Fu.pp_print_minimal e
            rpar
            (pp_print_delimited (pp_print_expr ~temp:temp cx)) es
      end
  | Product [e] ->
      fmt_expr ~temp:temp cx e
  | Product (e :: es) ->
      (* FIXME this should be a Fu.Big because \X is neither right nor
         left-associative. *)
      Fu.Op (
        "\\X",
        (fun ff -> fprintf ff "@ \\X "),
        (10, 13),
        Fu.Infix (Fu.Right, fmt_expr ~temp:temp cx e,
                  fmt_expr ~temp:temp cx (Product es @@ ew))
      )
  | Product _ -> Errors.bug ~at:ew "Expr.Fmt.fmt_expr: PRODUCT []"
  | Tuple es ->
      Fu.Atm begin
        fun ff ->
          fprintf ff "@[<b2><<%a>>@]"
            (pp_print_delimited (pp_print_expr ~temp:temp cx)) es
      end
  | Rect fs ->
      Fu.Atm (fun ff ->
                fprintf ff "@[<b1>[%a]@]"
                  (pp_print_delimited
                     (fun ff (v, e) ->
                        fprintf ff "@[<h>%s : %a@]" v (pp_print_expr ~temp:temp cx) e)) fs)
  | Record fs ->
      Fu.Atm (fun ff ->
               fprintf ff "@[<b1>[%a]@]"
                  (pp_print_delimited
                     (fun ff (v, e) ->
                        fprintf ff "@[<h>%s |-> %a@]" v (pp_print_expr ~temp:temp cx) e)) fs)
  | Except (e, xs) ->
      Fu.Atm (fun ff ->
                fprintf ff "@[<b3>[%a EXCEPT@ @[<v0>%a@]]@]"
                  (pp_print_expr ~temp:temp cx) e
                  (pp_print_delimited
                     (fun ff (tr, e) ->
                        fprintf ff "!@[<h>%a = %a@]"
                          (pp_print_delimited ~sep:(fun ff () -> ())
                             (fun ff -> function
                                | Except_dot s -> fprintf ff ".%s" s
                                | Except_apply e -> fprintf ff "[%a]" (pp_print_expr ~temp:temp cx) e))
                          tr
                          (pp_print_expr ~temp:temp cx)
                          e))
                  xs)
  | Dot (e, f) ->
      Fu.Op (".",
             (fun ff -> pp_print_string ff "."),
             (16, 16),
             Fu.Infix (Fu.Left, fmt_expr ~temp:temp cx e,
                       Fu.Atm (fun ff -> pp_print_string ff f)))
  | Sub (q, e, f) ->
      Fu.Atm (fun ff ->
                fprintf ff "@[<h>%s@[<b2>%a@]%s%a@]"
                  (match q with Box -> "[" | _ -> "<<")
                  (pp_print_expr ~temp:temp cx) e
                  (match q with Box -> "]_" | _ -> ">>_")
                  (pp_print_expr ~temp:temp cx) f)
  | Tsub (q, e, f) ->
      Fu.Atm (fun ff ->
                fprintf ff "@[<h>%s@[<b2>%a@]%s%a@]"
                  (match q with Box -> "[][" | _ -> "<><<")
                  (pp_print_expr ~temp:temp cx) e
                  (match q with Box -> "]_" | _ -> ">>_")
                  (pp_print_expr ~temp:temp cx) f)
  | Fair (q, e, f) ->
      Fu.Big (fun ff ->
                fprintf ff "@[<h>%s_%a (%a)@]"
                  (match q with Weak -> "WF" | _ -> "SF")
                  (pp_print_with_parens (pp_print_expr ~temp:temp cx)) e
                  (pp_print_expr ~temp:temp cx) f)
  | Case (arms, oth) ->
      Fu.Big (fun ff ->
                fprintf ff "@[<v2>CASE %a%a@]"
                  (pp_print_delimited
                     ~sep:(fun ff () -> fprintf ff "@,[] ")
                     (fun ff (e, f) ->
                        fprintf ff "@[<b2>%a ->@ %a@]"
                          (pp_print_expr ~temp:temp cx) e
                          (pp_print_expr ~temp:temp cx) f))
                  arms
                  (fun ff -> function
                     | None -> ()
                     | Some oth ->
                         fprintf ff "@,[] @[<b2>OTHER ->@ %a@]"
                           (pp_print_expr ~temp:temp cx) oth)
                  oth)
  | String s ->
      Fu.Atm (fun ff ->
                fprintf ff "\"%s\"" s)
  | Num (m, "") ->
      Fu.Atm (fun ff -> pp_print_string ff m)
  | Num (m, n) ->
      Fu.Atm (fun ff -> fprintf ff "%s.%s" m n)
  | At _ ->
      Fu.Atm (fun ff -> pp_print_string ff "@")
  | Parens (e, {core = Nlabel (l, []) | Xlabel (l, [])}) -> begin
      let f = fmt_expr ~temp:temp cx e in
      match f with
        | Fu.Atm _ | Fu.Big _ ->
            Fu.Atm (fun ff -> fprintf ff "%s::%a" l Fu.pp_print_minimal f)
        | _ ->
            Fu.Atm (fun ff -> fprintf ff "%s::(%a)" l Fu.pp_print_minimal f)
    end
  | Parens (e, {core = Nlabel (l, xs)}) -> begin
      let fe = fmt_expr ~temp:temp cx e in
      let fmt = match fe with
        | Fu.Atm _ ->
            format_of_string "%s(%a)::%a"
        | Fu.Big _ ->
            format_of_string "%s(%a)::(%a)"
        | _ ->
            format_of_string "(%s(%a):: %a)"
      in
      Fu.Atm begin fun ff ->
        fprintf ff fmt
          l (pp_print_delimited pp_print_var) xs
          Fu.pp_print_minimal fe
      end
    end
  | Parens (e, {core = Xlabel (l, xs)}) ->
      let xs = List.map begin
        fun (h, x) ->
          try Ctx.string_of_ident (fst (Ctx.index (snd cx) x)) @@ h
          with _ -> ("¶" ^ string_of_int x) @@ h
      end xs in
      fmt_expr ~temp:temp cx (Parens (e, Nlabel (l, xs) @@ e) @@ e)
  | Parens (e, {core = Syntax}) ->
      fmt_expr ~temp:temp cx e
  | QuantTuply _
  | ChooseTuply _
  | SetStTuply _
  | SetOfTuply _
  | FcnTuply _ -> assert false

and pp_print_bang ff () =
  if Params.debugging "garish" then
    pp_print_as ff 1 "§"
  else
    pp_print_string ff "!"

and pp_print_sels cx ff sels =
  if sels <> [] then pp_print_bang ff () ;
  pp_print_delimited ~sep:pp_print_bang (pp_print_sel cx) ff sels

and pp_print_sel cx ff = function
  | Sel_down ->
      pp_print_string ff ":"
  | Sel_left ->
      pp_print_string ff "<<"
  | Sel_right ->
      pp_print_string ff ">>"
  | Sel_at ->
      pp_print_string ff "@"
  | Sel_num n ->
      pp_print_int ff n
  | Sel_inst args ->
      fprintf ff "@[<b1>(%a)@]"
        (pp_print_delimited (pp_print_expr cx)) args
  | Sel_lab (l, []) ->
      pp_print_string ff l
  | Sel_lab (l, args) ->
      fprintf ff "@[<b2>%s@,@[<b1>(%a)@]@]"
        l (pp_print_delimited (pp_print_expr cx)) args

and pp_print_lambda cx ff vss e =
  let vs = List.map fst vss in
  let (ecx, _) = adjs cx vs in
  fprintf ff "@[<b2>LAMBDA @[<hv0>%a@] :@ %a@]"
    (pp_print_delimited pp_print_vs) vss
    (pp_print_expr ecx) e

and pp_print_vs ff (v, shp) =
  fprintf ff "%s%a" v.core pp_print_shape shp

and pp_print_shape ff = function
  | Shape_expr -> ()
  | Shape_op n ->
      let unds = List.init n (fun _ -> "_") in
      fprintf ff "@[<hov1>(%a)@]"
        (pp_print_delimited pp_print_string) unds

and fmt_apply (hx, vx as cx) op args = match op.core, args with
  | Lambda (vss, e), _ ->
      Fu.Op (
        " ",
        (fun ff -> pp_print_space ff ()), (20, 20),
        Fu.Infix (
          Fu.Left,
          Fu.Big (fun ff -> pp_print_lambda cx ff vss e),
          Fu.Atm (
            fun ff ->
              fprintf ff "(%a)" (pp_print_delimited (pp_print_expr cx)) args
          )
        )
      )
  | Bang _, [] ->
      fmt_expr cx op
  | Bang _, _ ->
      Fu.Atm begin
        fun ff ->
          fprintf ff "@[<b2>%a@[<b1>(%a)@]@]"
            (pp_print_expr cx) op
            (pp_print_delimited (pp_print_expr cx)) args
      end
  | Internal Builtin.Prime, [e] when !Params.notl ->
      Fu.Op (
        "#$",
        (fun ff -> pp_print_string ff "#$"),
        (15, 15),
        Fu.Postfix (fmt_expr cx e)
      )
  | Internal (Builtin.Box false), [e] when Params.debugging "temporal" ->
      Fu.Atm (fun ff -> fprintf ff "[](%a)" (pp_print_expr cx) e)
  | Internal (Builtin.Box false), [e]
  | Internal Builtin.Unprimable, [e] ->
      fmt_expr cx e
  | Internal Builtin.Irregular, [e] ->
      Fu.Atm begin
        fun ff ->
          fprintf ff "@[<h>@<1>%s%a@<1>%s@]"
            "<[" (pp_print_expr cx) e "]>"
      end
  | _ ->
      let top = match op.core with
        | Ix n ->
            let id =
              if n < 0 then "#$$" ^ string_of_int (abs n)
              else if n = 0 then "#$0"
              else if n <= Ctx.length vx then
                Ctx.string_of_ident (fst (Ctx.index vx n))
              else if n - Ctx.length vx <= Deque.size hx then
                hyp_name (Option.get (Deque.nth ~backwards:true hx (n - Ctx.length vx - 1)))
              else "#$" ^ string_of_int n
            in
            let top = Optable.lookup id in
            if Params.debugging "ix" then
              { top with Optable.name = top.Optable.name ^ "#$" ^ string_of_int (abs n) }
            else top
        | Opaque s ->
            let top = Optable.lookup s in
            (* coalescing leads to this case, prepending "?" to the newly
            introduced identifiers. *)
            if Ctx.try_print_src (snd cx)
              then top
              else { top with Optable.name = "?" ^ top.Optable.name }
        | Internal b ->
            Optable.standard_form b
        | _ ->
            Util.eprintf ~at:op
              "Cannot print this (con: %d):@\n  @[%a@]@."
              (Property.unsafe_con op)
              (pp_print_expr cx) op ;
            failwith "impossible"
      in
      begin
        if List.length args = 0 then
          Fu.Atm (fun ff -> pp_print_string ff top.Optable.name)
        else match top.Optable.fix with
          | Optable.Nonfix ->
              Fu.Atm begin
                fun ff ->
                  fprintf ff "@[<b2>%s@[<b1>(%a)@]@]"
                    top.Optable.name
                    (pp_print_delimited (pp_print_expr cx)) args
              end
          | Optable.Prefix when List.length args = 1 ->
              let n = top.Optable.name in
              let fmt =
                if is_letter n.[String.length n - 1]
                then format_of_string "%s@ "
                else format_of_string "%s"
              in
              Fu.Op (
               top.Optable.name,
               (fun ff -> fprintf ff fmt top.Optable.name),
               top.Optable.prec,
               Fu.Prefix (fmt_expr cx (List.hd args))
             )
          | Optable.Postfix when List.length args = 1 ->
              Fu.Op (
                top.Optable.name,
                (fun ff -> fprintf ff "%s" top.Optable.name),
                top.Optable.prec,
                Fu.Postfix (fmt_expr cx (List.hd args))
              )
          | Optable.Infix assoc when List.length args = 2 ->
              let fmt =
                if top.Optable.name = ".."
                then format_of_string "%s"
                else format_of_string "@ %s "
              in
              Fu.Op (
                top.Optable.name,
                (fun ff -> fprintf ff fmt top.Optable.name),
                top.Optable.prec,
                Fu.Infix (
                  (match assoc with
                     | Optable.Left -> Fu.Left
                     | Optable.Right -> Fu.Right
                     | Optable.Non -> Fu.Non),
                  fmt_expr cx (List.nth args 0),
                  fmt_expr cx (List.nth args 1)
                )
              )
          | _ ->
              Util.eprintf ~at:op "%s" (
                  "`Expr.Fmt`: arity mismatch for operator `" ^
                  top.Optable.name ^ "`, with " ^
                  (string_of_int (List.length args)) ^ " arguments.\n");
              failwith "`Expr.Fmt`: arity mismatch"
      end

and fmt_bounds cx bs =
  let (ecx, vs) = extend_bounds cx bs in
  let bs = List.map2 (fun (_, k, d) (v, _) -> (v, k, d)) bs vs in
  begin ecx, fun ff -> match bs with
     | [] -> assert false
     | (v, k, d) :: bs ->
         let chs = ref [] in
         let cch = ref [v] in
         let cd = ref d in
         List.iter begin
           fun (v, k, d) -> match d with
             | Ditto ->
                 cch := v :: !cch
             | _ ->
                 chs := (List.rev !cch, !cd) :: !chs ;
                 cch := [v] ;
                 cd := d
         end bs ;
         chs := (List.rev !cch, !cd) :: !chs ;
         let bss = List.rev !chs in
         pp_print_delimited (pp_print_chunk cx) ff bss
  end

and pp_print_chunk cx ff (vs, dom) =
  match dom with
    | No_domain ->
        pp_print_delimited pp_print_string ff vs
    | Domain dom ->
        fprintf ff "@[<hov0>%a@ \\in %a@]"
          (pp_print_delimited pp_print_string) vs
          (pp_print_expr cx) dom
    | Ditto ->
        fprintf ff "@[<hov0>%a@ \\in ??????@]"
          (pp_print_delimited pp_print_string) vs

and pp_print_bound cx ff (v, e) = match e with
  | None -> pp_print_string ff v
  | Some e ->
      fprintf ff "@[<h>%s \\in %a@]" v (pp_print_expr cx) e

and pp_print_expr ?(temp=false) cx ff e =
  Fu.pp_print_minimal ff (fmt_expr ~temp:temp cx e) ;

and pp_print_defn cx ff d =
  match d.core with
    | Operator (nm, {core = Lambda (vss, e)})
    | Bpragma (nm, {core = Lambda (vss, e)}, _) ->
        let vs = List.map fst vss in
        let (ncx, nm) = adj cx nm in
        let (ecx, _) = adjs cx vs in
        fprintf ff "@[<b2>%s@[<b1>(%a)@] ==@ %a@]"
          nm (pp_print_delimited pp_print_vs) vss
          (pp_print_expr ecx) e ;
        ncx
    | Operator (nm, e)
    | Bpragma (nm, e, _) ->
        let (ncx, nm) = adj cx nm in
        fprintf ff "@[<b2>%s ==@ %a@]"
          nm (pp_print_expr cx) e ;
        ncx
    | Instance (nm, i) ->
        let (ncx, nm) = adj cx nm in
        let (cx, vs) = adjs cx i.inst_args in
        fprintf ff "@[<b2>%a == %a@]"
          (fun ff -> function
             | [] -> pp_print_string ff nm
             | is ->
                 fprintf ff "%s (@[<b0>%a@])"
                   nm (pp_print_delimited pp_print_string) vs)
          i.inst_args
          (pp_print_instance cx) i ;
        ncx
    | Recursive (nm, shp) ->
       let (ncx, nm) = adj cx nm in
       fprintf ff "@[<b2>NEW CONSTANT %s%a@]" nm pp_print_shape shp;
       ncx

and pp_print_instance cx ff i =
  let pp_print_subst ff (v, e) =
    fprintf ff "@[<b2>%s <- %a@]"
      v.core (pp_print_expr cx) e in
  fprintf ff "@[<b2>INSTANCE %s%a@]"
    i.inst_mod
    (fun ff -> function
       | [] -> ()
       | subs ->
           fprintf ff "@ WITH@ %a"
             (pp_print_delimited pp_print_subst) subs)
    i.inst_sub

and pp_print_defns cx ff = function
  | [] -> cx
  | [d] ->
      pp_print_defn cx ff d
  | d :: ds ->
      let cx = pp_print_defn cx ff d in
      pp_print_cut ff () ;
      pp_print_defns cx ff ds

and pp_print_sequent  ?(temp=false) cx ff sq = match Deque.null sq.context with
  | true ->
      pp_print_expr cx ff sq.active ;
      cx
  | _ ->
      let (cx, chs) =
        Deque.fold_left begin
          fun (cx, chs) h ->
            let ch = (cx, h) in
            let cx = match h.core with
              | Fresh (nm, _, _, _) | Flex nm
              | Defn ({core = Operator (nm, _) | Instance (nm, _)
                              | Bpragma (nm,_,_) | Recursive (nm, _) },
                      _, _, _) ->
                  fst (adj cx nm)
              | Fact (_, _,_) ->
                  bump cx
              | FreshTuply _ ->
                  assert false  (* not implemented *)
            in (cx, ch :: chs)
        end (cx, []) sq.context in
      let chs = List.filter (fun (cx, h) -> not (elide h)) (List.rev chs) in
      if List.length chs > 0 then begin
        fprintf ff "@[<v0>ASSUME @[<v0>" ;
        pp_print_delimited begin
          fun ff (cx, h) -> ignore (pp_print_hyp ~temp:temp cx ff h)
        end ff chs ;
        fprintf ff "@]@\nPROVE  %a@]" (pp_print_expr ~temp:temp cx) sq.active
      end else pp_print_expr ~temp:temp cx ff sq.active ;
      cx

and pp_print_time bg ff tm = match (bg,tm) with
  | (true,Now) -> fprintf ff "(* %s *)" "non-[]"
  | _ -> fprintf ff ""

and pp_print_hyp ?(temp=false) cx ff h =
  if Params.debugging "hidden" then begin
    if is_hidden h then fprintf ff "(* hidden *)@\n"
  end ;
  match h.core with
    | Fresh (nm, shp, lc, b) ->
        (* minus hack *)
        let (ncx, nm) = adj cx nm in
        fprintf ff "NEW %s %s%a"
          (match lc with
             | Constant -> "CONSTANT"
             | State -> "STATE"
             | Action -> "ACTION"
             | Temporal -> "TEMPORAL"
             | Unknown -> "UNKNOWN")
          nm pp_print_shape shp ;
        (match b with
           | Unbounded
           | Bounded (_, Hidden) -> ()
           | Bounded (b, _) -> fprintf ff " \\in %a" (pp_print_expr ~temp:temp cx) b) ;
        ncx
    | FreshTuply _ -> assert false  (* not implemented *)
    | Flex nm ->
        let (ncx, nm) = adj cx nm in
        fprintf ff "NEW VARIABLE %s" nm ;
        ncx
    | Defn (d, wd, us, _) ->
        if Params.debugging "alldefs" then begin
          fprintf ff begin
            match wd with
              | Builtin -> format_of_string "(* builtin *)@\n"
              | Proof _ -> format_of_string "(* from proof *)@\n"
              | _ -> format_of_string ""
          end
        end ;
        pp_print_defn cx ff d
    | Fact (e, us, tm) ->
        let ncx = bump cx in
        fprintf ff "@[<h>%a %a@]" (pp_print_expr ~temp:temp cx) e (pp_print_time
        temp) tm;

        ncx

let string_of_expr cx e =
    let b = Buffer.create 10 in
    let fmt = Format.formatter_of_buffer b in
    Format.pp_set_max_indent fmt 35;
    Format.pp_set_max_boxes fmt 12;
    Format.pp_set_ellipsis_text fmt "...";
    ignore (pp_print_expr (cx, Ctx.dot) fmt e);
    Format.pp_print_flush fmt () ;
    Buffer.contents b
