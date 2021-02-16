(*
 * expr/parser.ml --- expressions (parsing)
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Property
open E_t
open Tla_parser.P
open Tla_parser
open Token

module Prop = Property

module Op = Optable
module B = Builtin

(*let b = ref false*)

let fixities =
  let fixities = Hashtbl.create 109 in
  let infix op prec assoc =
    Opr begin
      prec, Infix begin
        assoc, fun oploc a b ->
          let op = Util.locate op oploc in
          let loc = Loc.merge oploc (Loc.merge (Util.get_locus a) (Util.get_locus b)) in
            Util.locate (Apply (op, [a ; b])) loc
      end
    end in
  let bin_prod =
    Opr begin
      (10, 13), Infix begin
        Left, fun oploc a b ->
          let loc = Loc.merge oploc (Loc.merge (Util.get_locus a) (Util.get_locus b)) in
            Util.locate begin
              match a.core with
                | Product es -> Product (es @ [b])
                | _ -> Product [a ; b]
            end loc
      end
    end in
  let prefix op prec =
    Opr begin
      prec, Prefix begin
        fun oploc a ->
          let op = Util.locate op oploc in
          let loc = Loc.merge oploc (Util.get_locus a) in
            Util.locate (Apply (op, [a])) loc
      end
    end in
  let postfix op prec =
    Opr begin
      prec, Postfix begin
        fun oploc a ->
         let op = Util.locate op oploc in
          let loc = Loc.merge oploc (Util.get_locus a) in
            Util.locate (Apply (op, [a])) loc
      end
    end
  in
    Hashtbl.iter begin
      fun form top ->
        Hashtbl.add fixities form begin
          match top.Op.defn with
            | _ -> begin
                let defn = match top.Op.defn with
                  | Some bltin -> Internal bltin
                  | None -> Opaque top.Op.name
                in match top.Op.fix with
                  | Op.Prefix -> prefix defn top.Op.prec
                  | Op.Postfix -> postfix defn top.Op.prec
                  | Op.Infix ass ->
                      infix defn top.Op.prec begin
                        match ass with
                          | Op.Left -> Left
                          | Op.Right -> Right
                          | Op.Non -> Non
                      end
                  | _ ->
                      failwith "Nonfix operator in optable?!"
              end
        end
    end Op.optable ;
    Hashtbl.replace fixities "\\X" bin_prod ;
    Hashtbl.replace fixities "\\times" bin_prod ;
    fixities

let distinct =
  let module S = Set.Make (String) in
  let rec check seen = function
    | [] -> true
    | v :: vs ->
        not (S.mem v.core seen)
        && check (S.add v.core seen) vs
  in
    fun vs -> check S.empty vs

let hint = locate anyident

let rec expr b = lazy begin
  resolve (expr_or_op b);
end

and expr_or_op b is_start =
  choice [
    (* labels *)
    if is_start then
      locate (attempt (use label) <**> use (expr b))
      <$> (function {core = (l, e)} as bl ->
             [ Atm (Parens (e, l) @@ bl) ])
    else fail "not a labelled expression" ;

    (* bulleted lists *)

    if is_start then
      locate (use (bulleted_list b))
      <$> (fun bl -> [Atm bl])
    else fail "not a bulleted list" ;

    (* temporal subscripting *)

    if is_start then
      attempt begin
        locate (prefix "[]" >>> punct "[" >*> use (expr b) <<< punct "]_" <**> use (sub_expr b))
        <$> begin
          fun { core = (e, v) ; props = props } ->
            [Atm { core = Tsub (Box, e, v) ; props = props }]
        end
      end
    else fail "not a [] [_]_" ;

    if is_start then
      attempt begin
        locate (prefix "<>" >>> punct "<<" >>> use (expr b) <<< punct ">>_" <*> use (sub_expr b))
        <$> begin
          fun { core = (e, v) ; props = props } ->
            [Atm { core = Tsub (Dia, e, v) ; props = props }]
        end
      end
    else fail "not a <> <<_>>_" ;

    (* ?fix operators *)

    attempt anyop >>+ begin fun p pts ->
      match Hashtbl.find_all fixities p with
        | [] -> fail ("unknown operator " ^ p)
        | ops ->
            let non_test = function
              | Opr (_, Infix (_, ix)) ->
                  attempt (punct "(" >>> (use (expr b) <*> (punct "," >>> use (expr b))) <<< punct ")")
                  (* <<! [Printf.sprintf "args of nonfix_%s" p] *)
                  <$> (fun (e, f) -> [P.Atm (ix pts e f)])
              | Opr (_, Postfix ix) ->
                  attempt (punct "(" >>> use (expr b) <<< punct ")")
                  (* <<! [Printf.sprintf "args of nonfix_%s" p] *)
                  <$> (fun e -> [P.Atm (ix pts e)])
              | _ -> fail "Unnonable"
            in
              choice (List.map non_test ops @ [return ops pts])
    end ;

    (* record fields *)
    if not is_start then
      attempt begin
        locate (punct "." >>> anyname)
      end <$> begin
        fun sw ->
          [ P.Opr begin
              (17, 17),
              P.Postfix begin
                fun _ r ->
                  let loc = Loc.merge (Util.get_locus r) (Util.get_locus sw) in
                    Util.locate (Dot (r, sw.core)) loc
              end
            end ]
      end
    else fail "not a rproj" ;

    (* function arguments *)

    if not is_start then
      attempt begin
        locate (punct "[" >>> sep1 (punct ",") (use (expr b)) <<< punct "]")
      end
      <$> begin
        fun esw ->
          [ P.Opr begin
              (17, 17),
              P.Postfix begin
                fun oploc f ->
                  let loc = Loc.merge (Util.get_locus f) (Util.get_locus esw) in
                    Util.locate (FcnApp (f, esw.core)) loc
              end
            end ]
      end
    else fail "not a farg" ;

    (* nonfix operators *)

    if is_start then
      locate begin
        attempt (use (operator b))
        <*> use (opargs b)
        <*> optional (use (subref b))
      end <$> begin
        fun prs ->
          let ((op, args), sr) = prs.core in
          let e = match args with
            | [] -> op
            | _ -> Apply (op, args) @@ prs
          in match sr, op.core with
            | None, Opaque x when x.[0] = '<' ->
               (* A step name is more like an empty subref than an ident. *)
               [ P.Atm (Bang (e, []) @@ prs) ]
            | None, _ -> [ P.Atm e ]
            | Some sr, _ -> [ P.Atm (Bang (e, sr) @@ prs) ]
      end
    else fail "not an opapp" ;

    (* complex expressions *)

    use (complex_expr b) <$> (fun e -> [P.Atm e]) ;
  ]

and label = lazy begin
  locate begin
    anyident <*> choice [
      punct "(" >>> sep1 (punct ",") (locate anyident) <<< punct ")" ;
      succeed [] ;
    ] <<< punct "::"
    <$> (fun (l, ns) -> Nlabel (l, ns))
  end
end

and opargs b = lazy begin
  optional begin
    punct "(" >*> sep1 (punct ",") (use (oparg b)) <<< punct ")"
  end <$> Option.default []
end

and subref b = lazy begin
  punct "!" >*> sep1 (punct "!") (use (sel b))
end

and sel b = lazy begin
  choice [
    choice [ anyident ; anyop ] <**> optional (punct "(" >>> sep1 (punct ",") (use (oparg b)) <<< punct ")")
    <$> (fun (l, args) -> match args with
           | None -> Sel_lab (l, [])
           | Some args -> Sel_lab (l, args)) ;

    punct "(" >*> sep1 (punct ",") (use (oparg b)) <<< punct ")"
    <$> (fun args -> Sel_inst args) ;

    nat <$> (fun n -> Sel_num n) ;

    punct "<<" <!> Sel_left ;

    punct ">>" <!> Sel_right ;

    punct ":" <!> Sel_down ;

    punct "@" <!> Sel_at ;
  ]
end

and complex_expr b = lazy begin
  choice [
    (* IF ... THEN ... ELSE *)

    locate begin
      (kwd "IF" >*> use (expr b))
      <**> (kwd "THEN" >>> use (expr b))
      <**> (kwd "ELSE" >>> use (expr b))
    end <$> begin
      fun ({core = ((a, b), c)} as ite) ->
        { ite with core = If (a, b, c) }
    end ;

    (* LET ... IN ... *)

    locate begin
      kwd "LET" >*> star1 (use (defn b))
      <**> (kwd "IN" >>> use (expr b))
    end <$> begin
      fun ({core = (ds, e)} as letin) ->
        { letin with core =  Let (ds, e) }
    end;

    (* use sequent <$> (fun sq -> Sequent sq) ; *)

    (* quantifiers *)

    locate begin
      choice [ punct "\\A" <!> Forall ;
               punct "\\E" <!> Exists ;
             ]
      <**> use (bounds b)
      <**> (punct ":" >>> use (expr b))
    end <$> begin
      fun ({core = ((q, bs), e)} as quant) ->
        { quant with core = Quant (q, bs, e) }
    end ;

    locate begin
      choice [ punct "\\AA" <!> Forall ;
               punct "\\EE" <!> Exists ]
      <**> (sep1 (punct ",") hint <?> distinct)
      <**> (punct ":" >>> use (expr b))
    end <$> begin
      fun ({core = ((q, vs), e)} as tquant) ->
        { tquant with core = Tquant (q, vs, e) }
    end ;

    locate begin
      kwd "CHOOSE" >*> hint
      <*> optional (infix "\\in" >*> use (expr b))
      <**> (punct ":" >>> use (expr b))
    end <$> begin
      fun ({core = ((v, ran), e)} as choose) ->
        { choose with core = Choose (v, ran, e) }
    end ;

    locate begin
      kwd "CASE"
      >*> sep1 (prefix "[]") (use (expr b) <**> (punct "->" >>> use (expr b)))
      <*> optional (prefix "[]" >*> kwd "OTHER" >*> punct "->" >*> use (expr b))
    end <$> begin
      fun ({core = (arms, oth)} as case) ->
        { case with core = Case (arms, oth) }
    end ;

    use (atomic_expr b);
  ]
end

and atomic_expr b = lazy begin
  choice [
    locate begin
      punct "{" >>>
        choice [
          attempt (hint <*> (infix "\\in" >*> use (expr b))) <*> (punct ":" >*> use (expr b))
          <$> (fun ((v, ran), e) -> SetSt (v, ran, e)) ;

          attempt (use (expr b)<<< punct ":") <*> use (boundeds b)
          <$> (fun (e, bs) -> SetOf (e, bs)) ;

          sep (punct ",") (use (expr b))
          <$> (fun es -> SetEnum es)
        ]
      <<< punct "}"
    end ;

    locate begin
      punct "[" >>>
        choice [
          enabled (anyname <<< punct "|->") >*>
            sep1 (punct ",") (anyname <<< punct "|->" <**> use (expr b))
          <<< punct "]"
          <$> (fun fs -> Record fs) ;

          enabled (anyname <<< punct ":") >*>
            sep1 (punct ",") (anyname <<< punct ":" <*> use (expr b))
          <<< punct "]"
          <$> (fun fs -> Rect fs) ;

          begin
            let rec exspec b = lazy begin
              punct "!" >>> use (trail b) <<< infix "=" <*> (use (expr true)) (* choice [ attempt (punct "@" <!> At true);  use expr ] *)
            end
            and trail b = lazy begin
              star1 begin
                choice [
                  punct "." >>> anyname <$> (fun x -> Except_dot x) ;
                  punct "[" >>> use (expr b) <<< punct "]" <$> (fun e -> Except_apply e) ;
                ]
              end
            end in
              attempt (use (expr b) <<< kwd "EXCEPT")
              <**> sep1 (punct ",") (use (exspec b)) <<< punct "]"
              <$> (fun (e, xs) -> Except (e, xs))
          end ;

          attempt (use (boundeds b) <<< punct "|->") <**> use (expr b)
          <<< punct "]"
          <$> (fun (bs, e) -> Fcn (bs, e)) ;

          use (expr b) >>= begin fun e ->
            choice [
              punct "->" >*> use (expr b) <<< punct "]"
              <$> (fun f -> Arrow (e, f)) ;

              punct "]_" >>> use (sub_expr b)
              <$> (fun v -> Sub (Box, e, v)) ;
            ]
          end ;
        ]
    end ;

    locate begin
      punct "<<" >>>
        sep (punct ",") (use (expr b)) >>= begin
          function
            | [e] ->
                choice [
                  punct ">>_" >*> use (sub_expr b)
                  <$> (fun v -> Sub (Dia, e, v)) ;

                  punct ">>" <!> Tuple [e] ;
                ]
            | es ->
                punct ">>" <!> Tuple es
        end
    end ;

    locate begin
      punct "WF_" >*>
        use (sub_expr b) <**> optional (punct "(" >>> use (expr b) <<< punct ")")
      <$> (fun (v, e) ->
               match e with
                 | Some ex -> Fair (Weak, v, ex)
                 | None ->
                     begin match v.core with
                       | Bang (a,sr) -> let srev = List.rev sr in
                           begin match List.hd srev with
                             | Sel_lab (h,el) -> (*if List.length el = 1 then*)
                                 Fair (Weak, (Bang(a, (List.rev ((Sel_lab(h,[]))::(List.tl srev)))) @@ v), List.hd el)
                             | _ -> Errors.bug ~at:v "Expr.Parser.WF:1"
                           end
                       | _ -> Errors.set v "Expr.Parser.WF:2"; failwith "Expr.Parser.WF:2"
                     end
             )
    end ;

    locate begin
      punct "SF_" >*>
        use (sub_expr b) <**> optional (punct "(" >>> use (expr b) <<< punct ")")
      <$> (fun (v, e) ->
               match e with
                 | Some ex -> Fair (Strong, v, ex)
                 | None ->
                     begin match v.core with
                       | Bang (a,sr) -> let srev = List.rev sr in
                           begin match List.hd srev with
                             | Sel_lab (h,el) -> (*if List.length el = 1 then*)
                                 Fair (Strong, (Bang(a, (List.rev ((Sel_lab(h,[]))::(List.tl srev)))) @@ v), List.hd el)
                             | _ -> Errors.bug ~at:v "Expr.Parser.SF:1"
                           end
                       | _ -> Errors.set v "Expr.Parser.SF:2"; failwith "Expr.Parser.SF:2"
                     end
             )
    end ;
(*        use (sub_expr b) <**> (punct "(" >>> use (expr b) <<< punct ")")
      <$> (fun (v, e) -> Fair (Strong, v, e))
    end ;*)

    locate begin
      punct "@" <!> (At b)
    end ;

    use (reduced_expr b) ;
  ]
end

and reduced_expr b = lazy begin
  choice [
    (* parentheses *)
    punct "(" >>> use (expr b) <<< punct ")"
    <$> (fun e -> Parens (e, Syntax @@ e) @@ e) ;

    (* string *)
    locate begin
      scan begin
        function
          | STR s -> Some (String s)
          | _ -> None
      end
    end ;

    (* number *)
    locate begin
      scan begin
        function
          | NUM (m, n) -> Some (Num (m, n))
          | _ -> None
      end
    end ;

    locate (kwd "TRUE" <!> Internal B.TRUE) ;
    locate (kwd "FALSE" <!> Internal B.FALSE) ;
    locate (kwd "BOOLEAN" <!> Internal B.BOOLEAN) ;
    locate (kwd "STRING" <!> Internal B.STRING) ;

    (* locate (punct "@" <!> At) ; *)
  ]
end

and sub_expr b = lazy begin
  choice [
    locate begin
      hint <*> optional (use (subref b))
    end <$> begin
      fun prs ->
        let (id, sr) = prs.core in
        let e = Opaque id.core @@ id in
        match sr with
          | None -> e
          | Some sr -> Bang (e, sr) @@ prs
    end ;

    use (atomic_expr b) ;
  ]
end

and bull_at bull where =
  P.scan begin
    fun t ->
      let module Loc = Loc in
        if t.Token.form = OP bull && Loc.column t.Token.loc.Loc.start = where
        then Some ()
        else None
  end

and bulleted_list b = lazy begin
  lookahead (scan begin
               function
                 | OP "/\\" -> Some "/\\"
                 | OP "\\/" -> Some "\\/"
                 | _ -> None
             end)
  >>+ fun bt loc ->
    get >>= fun px ->
      let module Loc = Loc in
      let bwhere = Loc.column loc.Loc.start in
      let newledge = { px with ledge = Loc.column loc.Loc.start + 1 } in
        star1 (bull_at bt bwhere >>> using newledge (use (expr b)))
        <$> (fun es -> match bt with
               | "\\/" -> List (Or, es)
               | _     -> List (And, es))
end

and operator b = lazy begin
  choice [
    locate begin
      kwd "LAMBDA" >*> sep1 (punct ",") hint
      <**> (punct ":" >>> use (expr b))
      <$> (fun (vs, e) -> Lambda (List.map (fun v -> (v, Shape_expr)) vs, e))
    end ;

    locate begin
      choice [
        anyident ;
        scan begin
            function
              | ST (`Num n, l, 0) -> Some (Printf.sprintf "<%d>%s" n l)
              | _ -> None
        end ;
      ] <$> (fun v -> Opaque v)
    end ;

    punct "(" >>> use (operator b) <<< punct ")" ;
  ]
end

and bounds b = lazy begin
  sep1 (punct ",") (sep1 (punct ",") hint <*> optional (infix "\\in" >*> use (expr b)))
  <$> begin
    fun bss ->
      let vss = List.map begin
        fun (vs, dom) -> match dom with
          | None ->
              List.map (fun v -> (v, Constant, No_domain)) vs
          | Some dom ->
              (List.hd vs, Constant, Domain dom)
              :: List.map (fun v -> (v, Constant, Ditto)) (List.tl vs)
      end bss in
      List.concat vss
  end
end

and boundeds b = lazy begin
  sep1 (punct ",") (sep1 (punct ",") hint <*> (infix "\\in" >*> use (expr b)))
  <$> begin
    fun bss ->
      let vss = List.map begin
        fun (vs, dom) ->
          (List.hd vs, Constant, Domain dom)
          :: List.map (fun v -> (v, Constant, Ditto)) (List.tl vs)
      end bss in
      List.concat vss
  end
end


(* pragmas *)

and float =
  number <$> (fun (m, n) ->
                float_of_string (Printf.sprintf "%s.%s0" m n))


and read_method_by = lazy begin
  ident "by" >>> use read_method_args <$> (fun l -> l)
end

(* FIXME remove this syntax; for the moment, treat it like "by" *)
and read_method_set = lazy begin
  ident "set" >>> use read_method_args <$> (fun l -> l)
end

and read_new_method = lazy begin
  pragma (star (choice [use read_method_by; use read_method_set]))
end

and read_method_args = lazy begin
    punct "(" >*> sep1 (punct ";") (use (read_method_arg)) <<< punct ")"
end

and read_method_arg = lazy begin
      hint <*> (punct ":" >*> use string_or_float_of_expr)
end


and string_val = lazy begin
  str <$> fun s -> Bstring s
end

and float_val = lazy begin
  float <$> fun s -> Bfloat s
end

and expr_def = lazy begin
   punct "@" <!> Bdef
end

and string_or_float_of_expr = lazy begin
  choice [ use string_val;
           use expr_def;
           use float_val;
         ]
end




(* definitions *)

and defn b = lazy begin
  locate (use (ophead b) <<< punct "==") >>= fun ({core = head} as oph) ->
    commit begin
      choice [
        locate (use (instance b))
        <$?> (fun i ->
                match head with
                | `Op (h, args) ->
                    let args = List.map fst args in
                    let loc = Loc.merge (Util.get_locus oph) (Util.get_locus i) in
                      Some (Util.locate (Instance (h, { i.core with inst_args = args })) loc)
                | _ ->
                    None) ;

        (* ajout *)

        use (expr b) <*> optional (use read_new_method) <$>
          begin
          fun (e,o) ->
            let loc = Loc.merge (Util.get_locus oph) (Util.get_locus e) in
            let op =
              match o with
                | Some (l) ->
                    begin
                      match head with
                        | `Op (h, args) ->
                            begin
                              match args with
                                | [] -> Bpragma (h, e, l)
                                | _ -> Bpragma (h,
                                                (Util.locate (Lambda (args, e)) loc),
                                                l)
                            end
                        | `Fun (h, args) ->  assert false (*** FIXME add error message ***)
                    end
                | None ->
                    begin
                      match head with
                        | `Op (h, args) ->
                            begin
                              match args with
                                | [] -> Operator (h, e)
                                | _ -> Operator (h, Util.locate (Lambda (args, e)) loc)
                            end
                        | `Fun (h, args) ->
                            Operator (h, Util.locate (Fcn (args, e)) loc)
                    end
            in Util.locate op loc
          end;

(*        use (expr b) <$> begin
          fun e ->
            let loc = Loc.merge (Util.get_locus oph) (Util.get_locus e) in
            let op = match head with
              | `Op (h, args) -> begin
                  match args with
                    | [] -> Operator (h, e)
                    | _ -> Operator (h, Util.locate (Lambda (args, e)) loc)
                end
              | `Fun (h, args) ->
                  Operator (h, Util.locate (Fcn (args, e)) loc)
            in Util.locate op loc
        end ;*)
      ]
    end
end

and ophead b = lazy begin
  choice [
    locate anyprefix <*> hint <$> (fun (h, u) -> `Op (h, [u, Shape_expr])) ;
    hint >>= fun u ->
      choice [
        locate anypostfix <$> (fun h -> `Op (h, [u, Shape_expr])) ;

        locate anyinfix <*> hint <$> (fun (h, v) -> `Op (h, [u, Shape_expr ; v, Shape_expr])) ;

        punct "[" >>> use (bounds b) <<< punct "]"
        <$> (fun args -> `Fun (u, args)) ;

        optional (punct "(" >>> sep1 (punct ",") ((use opdecl)) <<< punct ")")
        <$> (function
               | None -> `Op (u, [])
               | Some args -> `Op (u, args)) ;

      ] ;
  ]
end

and opdecl = lazy begin
  choice [
    locate anyprefix <<< punct "_"
    <$> (fun h -> (h, Shape_op 1)) ;

    punct "_" >*>
      choice [
        locate anypostfix
        <$> (fun h -> (h, Shape_op 1)) ;

        locate anyinfix <<< punct "_"
        <$> (fun h -> (h, Shape_op 2))
      ] ;

    hint <*> optional (punct "(" >>> sep1 (punct ",") (punct "_") <<< punct ")")
    <$> begin
      fun (h, args) -> match args with
        | None -> (h, Shape_expr)
        | Some args ->
            (h, Shape_op (List.length args))
    end ;
  ]
end

and oparg b = lazy begin
  alt [
    use (expr b);

    locate anyop
    <$> (fun op ->
           if Hashtbl.mem Optable.optable op.core then
             let top = Hashtbl.find Optable.optable op.core in
             match top.Optable.defn with
               | Some bin -> { op with core = Internal bin }
               | None -> { op with core = Opaque op.core }
           else { op with core = Opaque op.core }) ;
  ]
end

and instance b = lazy begin
  kwd "INSTANCE" >*> anyident
  <*> optional (kwd "WITH" >*> use (subst b))
  <$> (fun (m, sub) ->
         { inst_args = [] ;
           inst_mod = m ;
           inst_sub = Option.default [] sub })
end

and subst b = lazy begin
  let exprify op = return (Opaque op) in
  sep1 (punct ",")
    (choice [ hint ; locate anyop ]
     <**> (punct "<-" >>> choice [ use (expr b) ; locate (anyop >>+ exprify) ]))
end

and hyp b = lazy begin locate begin
  choice [
    optional (kwd "NEW") >>= begin fun nk ->
      choice [
        kwd "VARIABLE" >*> hint <$> (fun v -> (Flex v)) ;
        choice [
          kwd "STATE" <!> State ;
          kwd "ACTION" <!> Action ;
          kwd "TEMPORAL" <!> Temporal ;
          (if Option.is_some nk then
             optional (kwd "CONSTANT") <!> 1
           else
             kwd "CONSTANT" <!> 2) <!> Constant ;
        ] <**> alt [ hint <*> (infix "\\in" >*> use (expr b)) <$> (fun (v, b) -> (v, Shape_expr, Bounded (b, Visible))) ;
                     (use opdecl) <$> (fun (v, shp) -> (v, shp, Unbounded)) ]
        <$> (fun (lev, (v, shp, ran)) -> (Fresh (v, shp, lev, ran))) ;
      ]
    end ;

    locate (optional (hint <<< punct "::") <*> use (expr_or_sequent b))
    <$> begin
      fun le -> match le.core with
        | (None, e) -> Fact (e, Visible, NotSet)
        | (Some l, e) -> Fact (Parens (e, Xlabel (l.core, []) @@ l) @@ le,
        Visible, NotSet)
    end ;
  ]
end end

and sequent b = lazy begin
  kwd "ASSUME" >*> sep1 (punct ",") (use (hyp b))
  <**> (kwd "PROVE" >>> use (expr b))
  <$> (fun (hs, e) -> { context = Deque.of_list hs ; active = e }) ;
end

and expr_or_sequent b = lazy begin
  alt [
    use (expr b) ;
    locate (use (sequent b)) <$> (fun sq -> { sq with core = Sequent sq.core }) ;
  ]
end
