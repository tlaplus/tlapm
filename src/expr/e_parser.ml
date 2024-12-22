(* Parser of expressions.

Copyright (C) 2008-2010  INRIA and Microsoft Corporation
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


type boundeds = bounded list
    (* The `option` is present only to avoid
    code repetition in the parsing of rigid
    quantification (\A, \E).

    Specifically, to enable representing in
    a single type the value returned by the
    function `func_boundeds`, and the value
    returned by `names`.

    Apart from this corner, `func_boundeds`
    itself always returns declarations *with*
    domain-bounds, *and* all other calls to
    `func_boundeds` (i.e., except for the call
    from rigid quantification) involve only
    boundeds, so `option` is unnecessary there,
    and complicates the code.
    *)
and bounded = declared * (expr option)
and declared =
    | Flat of Util.hints
    | Tuply of Util.hints


let tuple_of_names = angle names


let has_tuply_bounded
        (boundeds: boundeds):
            bool =
    let is_tuply_bounded (names, _) =
        match names with
        | Tuply _ -> true
        | _ -> false in
    List.exists
        is_tuply_bounded boundeds


let make_dittos
        (names: Util.hints)
        (dom: expr)
        (make_bound:
                Util.hint ->
                bound_domain ->
                    'a):
            'a list =
    match names with
    | name :: rest ->
        make_bound name (Domain dom) ::
            List.map (fun name -> make_bound name Ditto) rest
    | [] -> assert false


let make_unboundeds
        (names: Util.hints):
            bounds =
    let make_bound name = (
        name, Constant, No_domain) in
    List.map make_bound names


let make_ditto_bounds
        (names: Util.hints)
        (dom: expr):
            bounds =
    let make_bound name d = (
        name, Constant, d) in
    make_dittos names dom make_bound


let make_ditto_tuply_bounds
        (names: Util.hints)
        (dom: expr):
            tuply_bounds =
    let make_bound name d = (
        Bound_name name, d) in
    make_dittos names dom make_bound


let bounds_of_boundeds
        (boundeds: boundeds):
            bounds =
    (* Return bounds from boundeds.

    Asserts that no item in `boundeds`
    is tuply.
    *)
    assert (not (has_tuply_bounded boundeds));
    let mapper =
        function
        | (Flat names, Some dom) ->
            make_ditto_bounds names dom
        | (Flat names, None) ->
            make_unboundeds names
        | _ ->
            assert false in
    let lists = List.map mapper boundeds in
    List.concat lists


let tuply_bounds_of_boundeds
        (boundeds: boundeds):
            tuply_bounds =
    (* Return tuply bounds from boundeds.

    Asserts that each item in `boundeds`
    has a domain-bound.
    Asserts that at least one item in
    `boundeds` is tuply.
    *)
    assert (has_tuply_bounded boundeds);
    let mapper =
        function
        | (Flat names, Some dom) ->
            make_ditto_tuply_bounds
                names dom
        | (Tuply names, Some dom) ->
            [(Bound_names names,
              Domain dom)]
        | (_, None) ->
            assert false in
    let lists = List.map
        mapper boundeds in
    List.concat lists


let make_quantifier_from_boundeds
        (quantifier: quantifier)
        (boundeds: boundeds)
        (predicate: expr):
            expr_ =
    if has_tuply_bounded boundeds
    then
        let bs = tuply_bounds_of_boundeds
            boundeds in
        QuantTuply (
            quantifier,
            bs,
            predicate)
    else
        let bs = bounds_of_boundeds
            boundeds in
        Quant (
            quantifier,
            bs,
            predicate)


let make_choose_from_boundeds
        (boundeds: boundeds)
        (predicate: expr):
            expr_ =
    match boundeds with
    | [(Flat [name], Some dom)] ->
        (* `Some` above works
        as an assertion. *)
        Choose (
            name,
            Some dom,
            predicate)
    | [(Tuply names, Some dom)] ->
        (* `Some` above works as
        an assertion. *)
        ChooseTuply (
            names,
            Some dom,
            predicate)
    | _ ->
        assert false


let make_setst_from_boundeds
        (boundeds: boundeds)
        (predicate: expr):
            expr_ =
    match boundeds with
    | [(Flat [name], Some dom)] ->
        SetSt (
            name,
            dom,
            predicate)
    | [(Tuply names, Some dom)] ->
        SetStTuply (
            names,
            dom,
            predicate)
    | _ ->
        assert false


let make_setof_from_boundeds
        (elem: expr)
        (boundeds: boundeds):
            expr_ =
    if has_tuply_bounded boundeds
    then
        let bs = tuply_bounds_of_boundeds
            boundeds in
        SetOfTuply (elem, bs)
    else
        let bs = bounds_of_boundeds
            boundeds in
        SetOf (elem, bs)


let make_fcn_from_boundeds
        (boundeds: boundeds)
        (value: expr):
            expr_ =
    if has_tuply_bounded boundeds
    then
        let bs = tuply_bounds_of_boundeds
            boundeds in
        FcnTuply (bs, value)
    else
        let bs = bounds_of_boundeds
            boundeds in
        Fcn (bs, value)


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
                  attempt (punct "(" >>> (use (expr b) <*> (comma_symbol >>> use (expr b))) <<< punct ")")
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
        locate (punct "[" >>> comma1 (use (expr b)) <<< punct "]")
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
      punct "(" >>> names <<< punct ")" ;
      succeed [] ;
    ] <<< punct "::"
    <$> (fun (l, ns) -> Nlabel (l, ns))
  end
end

and opargs b = lazy begin
  optional begin
    punct "(" >*> comma1 (use (oparg b)) <<< punct ")"
  end <$> Option.default []
end

and subref b = lazy begin
  punct "!" >*> sep1 (punct "!") (use (sel b))
end

and sel b = lazy begin
  choice [
    choice [ anyident ; anyop ] <**> optional (punct "("
        >>> comma1 (use (oparg b)) <<< punct ")")
    <$> (fun (l, args) -> match args with
           | None -> Sel_lab (l, [])
           | Some args -> Sel_lab (l, args)) ;

    punct "(" >*> comma1 (use (oparg b)) <<< punct ")"
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

    (* constant quantification
    for example:
        \E x, y, z:  x = y
        \E x \in S, <<y, z>> \in A \X B:  x = y

    Each constant quantifier can contain either:

    - only unbounded constant declarations, for example:
      `\E x, y, z:  x = y`, or

    - only bounded constant declarations:
      `\E x \in S,  y, z \in R:  x = z`,

    but not both bounded and unbounded.
    Bounded and unbounded declarations can be represented
    using nested quantifiers, for example:

    `\E x \in S:  \E y, z:  x = z`

    Read Section 16.1.1 on pages 293--294 of the book "Specifying Systems",
    in particular page 294.

    The definitions of (bounded) tuple declarations in quantifiers are:

    \E <x1, ..., xk>> \in S:  p ==
        \E x1, ..., xk:
            /\ <<x1, ..., xk>> \in S
            /\ p

    \A <x1, ..., xk>> \in S:  p ==
        \A x1, ..., xk:
            \/ <<x1, ..., xk>> \notin S
            \/ p
    *)
    locate begin
      choice [ punct "\\A" <!> Forall ;
               punct "\\E" <!> Exists ;
             ]
      <**> (quantifier_boundeds b)
      <**> (colon_expr b)
    end <$> begin
      fun ({core = ((q, boundeds), predicate)} as quant) ->
        let core = make_quantifier_from_boundeds
            q boundeds predicate in
        core @@ quant
    end ;

    locate begin
      choice [ punct "\\AA" <!> Forall ;
               punct "\\EE" <!> Exists ]
      <**> (names <?> distinct)
      <**> (colon_expr b)
    end <$> begin
      fun ({core = ((q, vs), e)} as tquant) ->
        { tquant with core = Tquant (q, vs, e) }
    end ;

    (* CHOOSE expressions

    examples:
        CHOOSE x:  TRUE
        CHOOSE x \in S:  TRUE
        CHOOSE <<x, y>> \in S:  TRUE

    Read Section 16.1.2 on pages 294--296 of the book "Specifying Systems",
    in particular page 296.

    The definition of a tuple declaration in
    CHOOSE expressions is:

    CHOOSE <<x1, ..., xn>>:  p ==
        CHOOSE y:
            \E x1, ..., xn:
                /\ y = <<x1, ..., xn>>
                /\ p
    *)
    locate begin
      kwd "CHOOSE"
        >*> alt [
            (* declared identifier *)
            hint
                <*> (colon_expr b)
                <$> (fun (v, e) -> Choose (v, None, e));

            (* unbounded tuple *)
            tuple_of_names
                <*> (colon_expr b)
                <$> (fun (vs, e) -> ChooseTuply (vs, None, e));

            (* bounded declared identifier or tuple *)
            use (func_boundeds b)
                <**> (colon_expr b)
                <$> (fun (boundeds, predicate) ->
                        make_choose_from_boundeds
                            boundeds predicate)
            ]
    end;

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
      (* set constructor *)
      punct "{" >>>
        choice [
          (* subset axiom, for example:
              {x \in S:  x + 1}
              {<<x, y>> \in S:  x = y}

          The definition of a (bounded) tuple declaration in
          the subset axiom is:

          {<<x1, ..., xn>> \in S:  p} ==
            {y \in S:
                \E x1, ..., xn:
                    /\ y = <<x1, ..., xn>>
                    /\ p

          Section 16.1.6 on pages 299--301 of the book "Specifying Systems",
          specifically page 301
          *)
          attempt (use (func_boundeds b))
            <*> (punct ":" >*> use (expr b))
            <$> begin
                fun (boundeds, predicate) ->
                    make_setst_from_boundeds
                        boundeds predicate
                end
          ;

          (* axiom scheme of replacement
          for example:  {x + 1:  x \in S}

          The definition of (bounded) tuple declarations in
          the axiom scheme of replacement is:

          {e:  <<x1, ..., xn>> \in S} ==
            {
                (LET
                    z == CHOOSE <<x1, ..., xn>>:  y = <<x1, ..., xn>>
                    x1 == z[1]
                    ...
                    xn == z[n]
                IN
                    e):  y \in S}

          Section 16.1.6 on pages 299--301 of the book "Specifying Systems",
          specifically page 301
          *)
          attempt (use (expr b) <<< colon)
            <*> use (func_boundeds b)
            <$> begin
                fun (elem, boundeds) ->
                make_setof_from_boundeds elem boundeds
                end
          ;

          (* set enumeration
          for example:  {1, 2, 3}

          Section 16.1.6 on pages 299--301 of the book "Specifying Systems",
          specifically page 300
          *)
          comma_exprs b
          <$> (fun es -> SetEnum es)
        ]
      <<< punct "}"
    end ;

    locate begin
      punct "[" >>>
        choice [
          (* Record constructor:  [name1 |-> e1, ...] *)
          enabled (anyname <<< mapsto) >*>
            (comma1 (anyname <<< mapsto <**> use (expr b)))
          <<< punct "]"
          <$> (fun fs -> Record fs) ;

          (* Set of records:  [name1: Values1, ...] *)
          enabled (anyname <<< colon) >*>
            (comma1 (anyname <<< colon <*> use (expr b)))
          <<< punct "]"
          <$> (fun fs -> Rect fs) ;

          (* EXCEPT expression, examples:

          [f EXCEPT ![1] = 2]
          [f EXCEPT ![1] = 3, ![2] = 4]
          [f EXCEPT ![1, 2] = 3]
          [f EXCEPT !["a"] = 3, !["b"] = 4]
          [f EXCEPT !.a = 3, !.b = 4]
          [f EXCEPT !.a = 3, !["b"] = 4]
          *)
          begin
            let rec exspec b = lazy begin
              (* except equality, examples:

              ![1] = 2
              !["a"] = 2
              !.a = 2
              ![1, 2] = 3
              *)
              punct "!" >>> use (trail b) <<< infix "=" <*> (use (expr true))
              (* choice [ attempt (punct "@" <!> At true);  use expr ] *)
            end
            and trail b = lazy begin
              star1 begin
                choice [
                  (* field reference:  .name *)
                  punct "." >>> anyname <$> (fun x -> Except_dot x) ;
                  (* application, examples:

                  [arg]
                  [arg1, arg2]
                  *)
                  punct "[" >>> alt [
                        (* single expression within square brackets:  [arg] *)
                        (use (expr b)) <<< punct "]";
                        (* comma-separated list of expressions,
                        within square brackets:  [arg1, ..., argN] *)
                        (comma1_exprs b)
                            <$> (fun es -> noprops (Tuple es))
                            <<< punct "]"
                    ]
                    <$> (fun e -> Except_apply e) ;
                ]
              end
            end in
              attempt (use (expr b) <<< kwd "EXCEPT")
              <**> comma1 (use (exspec b)) <<< punct "]"
              <$> (fun (e, xs) -> Except (e, xs))
          end ;

          (* Function constructor, examples:

          [x \in S |-> e]
          [<<x, y>> \in S \X R |-> e]
          [<<x, y>> \in S \X R, z \in Q |-> e]

          Only bounded declarations are allowed in function constructors.
          Read Section 16.1.7 on pages 301--304 of
          the book "Specifying Systems",
          in particular pages 303--304.
          *)
          attempt (use (func_boundeds b) <<< mapsto)
              <**> use (expr b)
              <<< punct "]"
              <$> (fun (boundeds, value) ->
                    make_fcn_from_boundeds boundeds value);

          use (expr b) >>= begin fun e ->
            choice [
              (* Set of functions:  [Domain -> Range] *)
              punct "->" >*> use (expr b) <<< punct "]"
              <$> (fun f -> Arrow (e, f)) ;

              (* Box action operator:  [A]_e *)
              punct "]_" >>> use (sub_expr b)
              <$> (fun v -> Sub (Box, e, v)) ;
            ]
          end ;
        ]
    end ;

    locate begin
      punct "<<" >>>
        comma_exprs b >>= begin
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
      kwd "LAMBDA" >*> names
      <**> (colon_expr b)
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


(* The function `bounds` is currently unused.

The function `bounds` allows including both bounded and unbounded
declarations in a single constructor.

Including both bounded and unbounded declarations in a single
quantifier constructor is not allowed in TLA+,
read Section 16.1.1 on pages 293--294 of the book "Specifying Systems",
in particular page 294.

Including both bounded and unbounded declarations in a single
`CHOOSE` constructor is not allowed in TLA+,
read Section 16.1.2 on pages 294--296 of the book "Specifying Systems",
in particular page 294.

Including unbounded declarations in a set constructor is
not allowed in TLA+,
read Section 16.1.6 on pages 299--301 of the book "Specifying Systems",
in particular page 301.

Including unbounded declarations in a function constructor or
function definition is not allowed in TLA+,
read Section 16.1.7 on pages 301--304 of the book "Specifying Systems",
in particular pages 303--304.
*)
and bounds b = lazy begin
  comma1 (names <*> optional (in_expr b))
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
  (* The function `boundeds` parses a list of only bounded declarations. *)
  comma1 (names <*> (in_expr b))
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


and quantifier_boundeds b =
    let wrap_names names =
        [(Flat names, None)] in
    let unboundeds =
        names
            <$> wrap_names in
    alt [
        use (func_boundeds b);
        unboundeds
        ]


and func_boundeds b = lazy begin
    (* Parse comma-separated bounded declarations.

    The declarations are separated by commas.

    Each declaration is either:
    - a comma-separated list of identifiers,
      followed by the lexeme `\in`,
      and an expression, or
    - a collection of identifiers described
      using TLA+ tuple syntax,
      followed by the lexeme `\in`,
      and an expression.

    Examples of such declarations:
    m \in S
    a, b \in R
    <<x, y, z>> \in S
    m \in S,  a, b \in R
    m \in S,  a, b \in R,  <<x, y>> \in A \X B

    Note that each declaration has a bound.
    Declarations of (lists of) identifiers
    and tuply declarations can appear in any
    order within the list of declarations.

    This parser returns a list of pairs
    (2-tuples), each a tuple of the form:
    `(declared, Some dom)`
    where:

    - `declared` is either:
      - `Flat names`, where `names` is
        a list of hints that appear as
        identifiers, each of which is
        bounded by `dom`, or
      - `Tuply names`, where `names` is
        a list of hints that appear as
        identifiers within a tuple that
        is bounded by `dom`

    - `dom` is an expression (the
      domain-bound)
    *)
    comma1 (choice [
        (* bounded constants, examples:

        m \in S
        a, b \in R
        *)
        (names <*> (in_expr b))
            <$> (fun (names, dom) -> (Flat names, Some dom));
        (* bounded tuples of constants, examples:

        <<x, y>> \in S
        <<a, b, c>> \in A \X B \X C
        *)
        (tuple_of_names <*> (in_expr b))
            <$> (fun (names, dom) -> (Tuply names, Some dom))
        ])
end


and colon_expr b =
    colon >>> use (expr b)


and in_expr b =
    (infix "\\in") >*> use (expr b)


and comma_exprs b =
    comma (use (expr b))


and comma1_exprs b =
    comma1 (use (expr b))


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
                        | `Fun (h, boundeds) ->
                            assert false  (* FIXME add error message *)
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
                        | `Fun (name, boundeds) ->
                            begin
                            let fcn_ = make_fcn_from_boundeds
                                boundeds e in
                            let fcn = Util.locate fcn_ loc in
                            Operator (name, fcn)
                            end
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
  let make_param name = (name, Shape_expr) in
  choice [
    (* prefix operator definition *)
    locate anyprefix
        <*> hint
        <$> (fun (op_name, param) ->
            let params = [make_param param] in
            `Op (op_name, params));
    hint >>= fun name_1 ->
      choice [
        (* postfix operator definition *)
        locate anypostfix
            <$> (fun op_name ->
                let params = [make_param name_1] in
                `Op (op_name, params));

        (* infix operator definition *)
        locate anyinfix
            <*> hint
            <$> (fun (op_name, name_2) ->
                let params = List.map
                    make_param [name_1; name_2] in
                `Op (op_name, params));

        (* function definition
        for example:
            f[x \in S, y \in Q] == ...
            f[<<x, y>> \in S \X Q, r \in T] == ...

        Only bounded declarations are allowed in function constructors.
        Read 16.1.7 on pages 301--304 of the book "Specifying Systems",
        in particular pages 303--304.

        This is why the function `func_boundeds` is called,
        instead of the function `bounds`.
        (Calling  the function `boundeds` would be correct,
        but would not parse tuple declarations within function
        definitions.)
        *)
        punct "[" >>> use (func_boundeds b) <<< punct "]"
        <$> (fun boundeds -> `Fun (name_1, boundeds));

        (* first-order-operator definition *)
        optional (
            punct "("
            >>> comma1 (use opdecl)
            <<< punct ")")
        <$> (function
               | None -> `Op (name_1, [])
               | Some args -> `Op (name_1, args))
      ]
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

    hint <*> optional (punct "(" >>> comma1 (punct "_") <<< punct ")")
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
  comma1
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
  kwd "ASSUME" >*> comma1 (use (hyp b))
  <**> (kwd "PROVE" >>> use (expr b))
  <$> (fun (hs, e) -> { context = Deque.of_list hs ; active = e }) ;
end

and expr_or_sequent b = lazy begin
  alt [
    use (expr b) ;
    locate (use (sequent b)) <$> (fun sq -> { sq with core = Sequent sq.core }) ;
  ]
end
