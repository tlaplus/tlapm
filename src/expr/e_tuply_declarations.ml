(* Expand declarations of the form <<x, ..., y>>.

Most traversals of this module expect
a concrete syntax tree,
i.e., identifiers before conversion to
De Bruijn indices.

Where otherwise, this is noted explicitly
in docstrings.
*)
module Deque = Deque
module Option = Option
open E_t
open E_t.From_hint
module Hint_map = Util.Coll.Hm
module String_set = Util.Coll.Ss
module Visit = E_visit

type hint = Util.hint
type hints = Util.hints

let noprops = Property.noprops
let nowhere = Property.nowhere
let (@@) = Property.(@@)
let ($$) = Property.($$)


let make_fresh_name
        (prefix: string)
        (name: hint):
            hint =
    (* Fresh identifier that contains `name`.

    Calls to this function pass as `name`
    the first identifier that appears within
    the tuply declaration, for example "x"
    from the declaration `\E <<x, y>> \in S: ...`.

    Currently, `name` is used as suffix of
    the fresh identifier, and this fresh
    identifier is declared as a constant
    in place of the tuply declaration
    (and is intended to be tuple-valued,
    which is the case when the domain-bound
    is a Cartesian product).
    *)
    (prefix ^ "#" ^ name.core) @@ name


let opaque_of (name: hint): expr =
    Opaque name.core @@ name


let tuple_of_names (names: hints): expr =
    let exprs = List.map opaque_of names in
    let name = List.hd names in
    make_tuple exprs $$ name


let make_eq (a: expr) (b: expr): expr =
    (* Return TLA+ equality `a = b`. *)
    let eqop = make_internal Eq in
    let eq = make_apply eqop [a; b] in
    eq $$ a


let components_of (product: expr) =
    (* Return list of product sets.

    Raises an exception if
    the expression `product`
    is not a Cartesian product,
    or has no components.
    *)
    match product.core with
    | Product [] -> failwith
        "parsing error"
    | Product items -> items
    | _ -> assert false


let is_cartesian_of
        (dom: expr)
        (elem: 'a list):
            bool =
    (* Detect Cartesian product matching element.

    Return `true` if `dom`:
    - is a Cartesian product
    - has same length as `elem`

    Raise exception if `dom` is a Cartesian
    product with no components,
    because there is no syntactic way of
    writing such a Cartesian product.

    (The empty Cartesian product *is* definable:
    any expression that equals the empty set
    defines the empty Cartesian product.
    For example, the expressions
    `{}` and `{} \X {1}`.

    What cannot be the result of parsing
    is a node in the syntax tree that
    represents a Cartesian product with
    no components, because such nodes result
    from parsing the binary operator `\X`.

    In other words, absence of components
    here suggests a parsing error.)

    Raise exception if `elem` is the empty list,
    because any tuply declaration
    must contain one or more identifiers.
    *)
    match elem with
    | [] -> failwith "parsing error"
    | _ -> ();
    match dom.core with
    | Product [] -> failwith "parsing error"
    | Product items ->
        (List.length items) =
        (List.length elem)
    | _ -> false


let assert_nonempty c what =
    match c with
    | [] -> failwith
        ("list of " ^ what ^ " is empty")
    | _ -> ()


let ops_of_qfr = function
    | Exists -> (make_internal Mem, And)
    | Forall -> (make_internal Notmem, Or)


(* This function is currently unused,
and present for testing purposes.
It is a monolithic implementation,
and without detection of Cartesian products.

The optimized implementation is implemented with
entry point the function `make_quant_from_tuply`,
and the optimization comprises of switching
between calling the function
`make_quant_from_cartesian_product_dom`
when a Cartesian product is recognized,
and otherwise the function
`make_quant_from_names_dom`.
*)
let make_quant_from_tuply_monolithic_nonoptimized
        (quantifier: quantifier)
        (tuply_bounds: tuply_bounds)
        (predicate: expr):
            expr =
    (* Translate tuply quantifier to simple form.

    In the presence of tuply declarations,
    bounded quantification is translated to
    unbounded quantification. This translation
    moves the bounds from *all* constants to
    the quantified expression.

    In the presence of *only* tuply declarations
    in the same quantifier, this translation
    corresponds to the definition of TLA+ syntax.

    If other declarations occur together with
    tuply declarations, in the *same* quantifier,
    then this translation removes structuring
    information that could be utilized later,
    in the backends.

    The alternative would be to first split
    each bounded quantifier into multiple
    bounded quantifiers, with one `\in`
    symbol per quantifier, and then apply
    this function to only those quantifiers
    that are tuply.

    There is no loss of generality by the approach
    taken in this function: the effect described
    above can be obtained by rewriting the
    composite bounded quantifier in the TLA+ file
    as multiple nested bounded quantifiers.

    For example, the expression:

        \A x \in S, <<y, z>> \in R:  x + y = z

    is translated to:

        \A x, y, z:
            \/ x + y = z
            \/ x \notin S
            \/ <<y, z>> \notin R

    whereas the expression:

        \A x \in S:  \A <<y, z>> \in R:  x + y = z

    is translated to:

        \A x \in S:  \A y, z:
            \/ x + y = z
            \/ <<y, z>> \notin R

    In the second case, the bounded quantification
    of `x` propagates to the backends.
    This additional structural information may
    be useful to specific backends.
    *)
    assert_nonempty tuply_bounds "bounds";
    let mem_op, bool_op = ops_of_qfr quantifier in
    let item_of e dom = make_apply mem_op [e; dom] in
    let reducer (optdom, out) bound =
        match bound with
        | (Bound_name name, Domain dom) ->
            let id = opaque_of name in
            (* name \in dom  (when \E), or
               name \notin dom  (when \A) *)
            let item = item_of id dom in
            (Some dom, item :: out)
        | (Bound_name name, Ditto) ->
            let dom = Option.get optdom in
            let id = opaque_of name in
            (* name \in dom  (when \E), or
               name \notin dom  (when \A) *)
            let item = item_of id dom in
            (optdom, item :: out)
        | (Bound_names names, Domain dom) ->
            (* <<... names ...>> *)
            let tuple = tuple_of_names names in
            (* <<... names ...>> \in dom
                (when \E), or
               <<... names ...>> \notin dom
                (when \A) *)
            let item = item_of tuple dom in
            (* `None` here resets the latest domain,
            in order to catch errors where
            a `(Bound_name _, Ditto)` is
            the next item after
            a `(Bound_names _, _)`. *)
            (None, item :: out)
        | _ -> assert false
            (* tuply declarations can appear only
            in bounded constant quantification.
            Read p.294 of the book
            "Specifying systems". *) in
    let _, items = List.fold_left reducer
        (None, []) tuply_bounds in
    let items = List.rev (predicate :: items) in
    (* when \E:
        /\ name \in dom1
        /\ <<... names ...>> \in dom2
        /\ ...
        /\ predicate

    when \A:
        \/ name \notin dom1
        \/ <<... names ...>> \notin dom2
        \/ ...
        \/ predicate
    *)
    let junction = make_junction bool_op items in
    (* Collect all declared identifiers,
    and declare them without bounds.
    *)
    let mapper bound =
        let make_bound name =
            make_unbounded name Constant in
        match bound with
        | (Bound_name name, (Domain _ | Ditto)) ->
            [make_bound name]
        | (Bound_names names, Domain _) ->
            List.map make_bound names
        | _ -> assert false
            (* see similar pattern-case above *)
        in
    let lists = List.map mapper tuply_bounds in
    let bounds = List.concat lists in
    Quant (quantifier, bounds, junction) @@ predicate


let rev_partition_tuply_bounds
        (tuply_bounds: tuply_bounds):
            tuply_bounds list =
    (* Return list of tuply bounds, one per domain.

    The returned list is in reverse order.

    The partitioning is done based on consecutive
    bounds. Dittos are grouped together with
    their preceding domain.
    Each tuply bound becomes a separate bound.

    For example:
        [(Bound_name _, A);
         (Bound_name _, B);
         (Bound_name _, Ditto);
         (Bound_name _, Ditto);
         (Bound_names _, C);
         (Bound_name _, D)]

    is partitioned into:
        [
            [(Bound_name _, Domain A)];

            [(Bound_name _, Domain B);
             (Bound_name _, Ditto);
             (Bound_name _, Ditto)];

            [(Bound_names _, Domain C)];

            [(Bound_name _, Domain D)]
        ]

    Sidenote: It is syntactically impossible to
    form an expression that will, after
    parsing, result in a `Ditto` succeeding
    a bound with `Bound_names` (i.e., a bound
    that is tuply):
        [(Bound_names _, Domain C);
         (_, Ditto)]
    *)
    let bump_group group out =
        match group with
        | [] -> out
        | _ ->
            let group = List.rev group in
            group :: out in
    let reducer (out, group) bound =
        let out, group = match bound with
            | (_, Domain _) ->
                let out = bump_group group out in
                (out, [])
            | (Bound_name _, Ditto) -> (out, group)
            | _ -> assert false in
        let group = bound :: group in
        (out, group) in
    let out = [] in
    let group = [] in
    let out, group = List.fold_left reducer
        (out, group) tuply_bounds in
    (* prepend reversed last group *)
    bump_group group out


let make_quant_from_simple_tuply_bounds
        (quantifier: quantifier)
        (tuply_bounds: tuply_bounds)
        (predicate: expr):
            expr =
    (* assert *)
    let asserter = function
        | (_, Ditto) -> ()
        | _ -> assert false in
    List.iter asserter (List.tl tuply_bounds);
    let asserter = function
        | (_, Domain _) -> ()
        | _ -> assert false in
    asserter (List.hd tuply_bounds);
    (* compute result *)
    let bound_of = function
        | (Bound_name name, dom) ->
            (name, Constant, dom)
        | _ -> assert false in
    let bounds = List.map bound_of tuply_bounds in
    Quant (quantifier, bounds, predicate) @@ predicate


let make_quant_from_names_dom
        (quantifier: quantifier)
        (names: hints)
        (dom: expr)
        (predicate: expr):
            expr =
    (* Translate one bounded tuply quantifier.
    *)
    assert_nonempty names "identifiers";
    let mem_op, bool_op = ops_of_qfr quantifier in
    let tuple = tuple_of_names names in
    let item = make_apply mem_op [tuple; dom] in
    let items = [item; predicate] in
    (* when `\E`:
        /\ <<... names ...>> \in dom
        /\ predicate
    when `\A`:
        \/ <<... names ...>> \notin dom
        \/ predicate
    *)
    let junction = make_junction bool_op items in
    let bound_of name = make_unbounded
        name Constant in
    let bounds = List.map bound_of names in
    Quant (quantifier, bounds, junction) @@ predicate


let make_quant_from_cartesian_product_dom
        (quantifier: quantifier)
        (names: hints)
        (domains: expr list)
        (predicate: expr):
            expr =
    (* Return quantified expression with bounds.

    The returned expression has the form:

    \Q name1 \in dom1, ..., nameN \in domN:
        predicate

    where `\Q` stands for `\E` or `\A`
    (depending on the argument `quantifier`).
    *)
    assert_nonempty names "identifiers";
    let bound_of name dom = (
        name, Constant, Domain dom) in
    let bounds = List.map2 bound_of names domains in
    Quant (quantifier, bounds, predicate) @@ predicate


let make_quant_from_one_tuply_bound
        (quantifier: quantifier)
        (names: hints)
        (dom: expr)
        (predicate: expr):
            expr =
    (* Detect Cartesian products, then optimize. *)
    assert_nonempty names "identifiers";
    let is_cartesian = is_cartesian_of dom names in
    (* REVIEW: check this again *)
    match dom.core with
    | Product domains when is_cartesian ->
        make_quant_from_cartesian_product_dom
            quantifier names domains predicate
    | _ ->
        make_quant_from_names_dom
            quantifier names dom predicate


let make_quant_from_tuply_bounds
        (quantifier: quantifier)
        (tuply_bounds: tuply_bounds)
        (predicate: expr):
            expr =
    (* Translate tuply bounds to quantification. *)
    match tuply_bounds with
    | [(Bound_names names, Domain dom)] ->
        make_quant_from_one_tuply_bound
            quantifier names dom predicate
    | (Bound_name _, Domain _) :: _ ->
        make_quant_from_simple_tuply_bounds
            quantifier tuply_bounds predicate
    | _ -> assert false


let make_quant_from_tuply
        (quantifier: quantifier)
        (tuply_bounds: tuply_bounds)
        (predicate: expr):
            expr =
    (* Translate tuply quantifier to simple form. *)
    assert_nonempty tuply_bounds "bounds";
    let partitioned = rev_partition_tuply_bounds
        tuply_bounds in
    let reducer predicate tuply_bound =
        make_quant_from_tuply_bounds
            quantifier tuply_bound predicate in
    List.fold_left reducer predicate partitioned


let def_of
        (name: hint)
        (definiens: expr):
            defn =
    Operator (name, definiens) @@ name


let num_of (pos: int): expr =
    (* Return index numeral made from `pos`. *)
    let integral = string_of_int pos in
    E_t.From_string.make_number integral ""


let defs_as_items_of
        (fcn: expr)
        (names: hints):
            defn list =
    (* Create one definition for each name.

    This function is used for creating the
    `LET` definitions that define each
    name of the tuply declaration as
    the n-th item of a fresh constant.

    This function is used only when the
    fresh constant is known to be
    tuple-valued, due to the domain-bound
    being a Cartesian product with the
    same number of components as the
    number of identifiers inside the
    tuply declaration.

    These definitions are used at
    the call site to construct
    a new `LET...IN` expression.
    For functions this `LET` wraps the
    value expression
    (the `e` in `[... |-> e]`).
    *)
    let make_def i name =
        (* 1-based index numeral *)
        let idx = num_of (i + 1) in
        let apl = make_fcn_app fcn idx in
        (* e.g., name == fcnbnd#x[1] *)
        def_of name apl in
    (* 0-based indexing *)
    List.mapi make_def names


let make_letin_from_tuply
        (y_name: hint)
        (names: hints)
        (expr: expr):
            expr =
    (* Detect Cartesian products,
    and in that case instead of introducing
    an existential quantifier and a conjunct,
    rewrite as a `LET` that defines the names
    as items in `y_name`.

    The following are examples of the two
    use cases of this function:

    ```tla
    CHOOSE <<name1, name2>> \in A \X B:
        P(name1, name2)
    ```

    which is translated to:

    ```tla
    CHOOSE y \in A \X B:
        LET
            name1 == y[1]
            name2 == y[2]
        IN
            P(name1, name2)
    ```

    and

    ```tla
    {<<name1, name2>> \in A \X B:
        P(name1, name2)}
    ```

    which is translated to:

    ```tla
    {y \in A \X B:
        LET
            name1 == y[1]
            name2 == y[2]
        IN
            P(name1, name2)}
    ```
    *)
    assert_nonempty names "identifiers";
    let fcn = opaque_of y_name in
    let defs = defs_as_items_of fcn names in
    make_let defs expr $$ expr


let make_exists_from_tuply
        (y_name: hint)
        (names: hints)
        (predicate: expr):
            expr =
    (* Return existential formula that encodes tuply.

    \E ... names ...:
        /\ y_name = <<... names ...>>
        /\ predicate
    *)
    assert_nonempty names "identifiers";
    let name = List.hd names in
    (* <<... names ...>> *)
    let names_tuple = tuple_of_names names in
    (* y_name = <<... names ...>> *)
    let eq = make_eq
        (opaque_of y_name) names_tuple in
    (* /\ y_name = <<... names ...>>
       /\ predicate *)
    let conjuncts = [eq; predicate] in
    let predicate = make_conjunction
        conjuncts $$ name in
    (* ... names ... *)
    let bounds = make_const_decls names in
    (* \E ... names ...:
        /\ y_name = <<... names ...>>
        /\ predicate
    *)
    make_exists bounds predicate $$ name


let make_choose_predicate_from_tuply
        (fresh_name: hint)
        (names: hints)
        (optdom: expr option)
        (predicate: expr):
            expr =
    let is_cartesian = match optdom with
        | Some dom -> is_cartesian_of dom names
        | None -> false in
    match is_cartesian with
    | true -> make_letin_from_tuply
        fresh_name names predicate
    | false -> make_exists_from_tuply
        fresh_name names predicate


let make_choose_from_tuply
        (names: hints)
        (optdom: expr option)
        (predicate: expr):
            expr =
    assert_nonempty names "identifiers";
    let fresh_name = make_fresh_name
        "choose" (List.hd names) in
    let predicate = make_choose_predicate_from_tuply
        fresh_name names optdom predicate in
    (* CHOOSE fresh_name:  \E ... names ...:
        /\ fresh_name = <<... names ...>>
        /\ predicate
    or
    CHOOSE fresh_name \in dom1 \X dom2:
        LET
            name1 == fresh_name[1]
            name2 == fresh_name[2]
        IN
            predicate
    *)
    Choose (fresh_name, optdom, predicate) @@ nowhere


let make_setst_from_tuply
        (names: hints)
        (dom: expr)
        (predicate: expr):
            expr =
    assert_nonempty names "identifiers";
    let fresh_name = make_fresh_name
        "setst" (List.hd names) in
    let predicate = make_choose_predicate_from_tuply
        fresh_name names (Some dom) predicate in
    (*  {fresh_name \in dom:
            \E ... names ...:
                /\ fresh_name = <<... names ...>>
                /\ predicate}
    or
        {fresh_name \in dom1 \X dom2:
            LET
                name1 == fresh_name[1]
                name2 == fresh_name[2]
            IN
                predicate}
    *)
    SetSt (fresh_name, dom, predicate) @@ nowhere


let domain_of (bound: bound_domain) =
    (* Return domain expression.

    Raises an exception if
    `bound` is unbounded or ditto.
    *)
    match bound with
    | Domain dom -> dom
    | _ -> assert false


let untuplify_setof_cartesian_bound
        (names: hints)
        (dom: expr):
            bounds * (defn list) =
    (* Simplify Cartesian bound of a `SetOf`.

    This simplification splits the
    Cartesian product into individual
    domain-bounds for the corresponding
    constants.

    For example `<<x, y>> \in S \X R` becomes
    `x \in S, y \in R`.

    So a tuple-valued constant and
    function application on numerals
    are not used at all here.

    When all tuply bounds have this
    form, then this simplification
    avoids introducing a `LET`
    construct.

    Asserts that:
    - `dom` is a Cartesian product and
    - `names` has length equal to
      the number of components
      in the Cartesian product `dom`.
    *)
    assert (is_cartesian_of dom names);
    let sets = components_of dom in
    (* name_1 \in d_1
       name_2 \in d_2 ... *)
    let mk_bound name d =
        (name, Constant, Domain d) in
    let bounds = List.map2
        mk_bound names sets in
    let defs = [] in
    (bounds, defs)


let untuplify_fcn_cartesian_bound
        (names: hints)
        (dom: expr):
            bounds * (defn list) =
    (* Simplify Cartesian bound of a `Fcn`.

    Asserts that:
    - `dom` is a Cartesian product and
    - `names` has length equal to
      the number of components
      in the Cartesian product `dom`.
    *)
    assert (is_cartesian_of dom names);
    let y_name = make_fresh_name
        "fcn" (List.hd names) in
    (* fcn#x *)
    let y_op = opaque_of y_name in
    (* fcn#x \in dom *)
    let bound = (
        y_name, Constant, Domain dom) in
    (* name_1 == fcn#x[1]
       name_2 == fcn#x[2] ... *)
    let defs = defs_as_items_of y_op names in
    ([bound], defs)


let untuplify_general_bound
        (names: hints)
        (dom: expr):
            bounds * (defn list) =
    (* `LET` definitions for tuply bound.

    Asserts that the bound expression
    does not have the form of
    a Cartesian product with number
    of components equal to the number
    of identifiers that appear in the
    tuply declaration.

    For the case of Cartesian products,
    call one of the functions:
    - `untuplify_setof_cartesian_bound`
    - `untuplify_fcn_cartesian_bound`
    *)
    assert (not
        (is_cartesian_of dom names));
    (* WARNING: using "fcn" here avoids also
    coincidence of identifier `y` with the
    identifier that is generated within the
    call to `make_choose_from_tuply` below. *)
    let y_name = make_fresh_name
        "fcn" (List.hd names) in
    let y_op = opaque_of y_name in
    let names_tuple = tuple_of_names names in
    let expr = make_eq y_op names_tuple in
    let choose = make_choose_from_tuply
        names None expr in
    let z_name = make_fresh_name
        "choose" y_name in
    (* bound: fcn#x \in dom, and as defs:

    z_name == CHOOSE choose#x:  \E x, y:
        /\ choose#x = <<x, y>>
        /\ fcn#x = <<x, y>>
    x == z_name[1]
    y == z_name[2]
    *)
    let z_def = def_of z_name choose in
    let z_op = opaque_of z_name in
    let x_defs = defs_as_items_of
        z_op names in
    let defs = z_def :: x_defs in
    let bound = (
        y_name, Constant, Domain dom) in
    ([bound], defs)


let make_let_for_setof_from_tuple
        (tuply_bounds: tuply_bounds)
        (value: expr)
        (is_setof: bool):
            expr * bounds =
    let mapper_of_tuply names dom =
        let simplify = is_cartesian_of
            dom names in
        match (simplify, is_setof) with
        | true, true ->
            untuplify_setof_cartesian_bound
                names dom
        | true, false ->
            untuplify_fcn_cartesian_bound
                names dom
        | false, _ ->
            untuplify_general_bound
                names dom in
    let mapper (id, dom) =
        match id with
        | Bound_name name ->
            let bound = (
                name, Constant, dom) in
            let defs = [] in
            [bound], defs
        | Bound_names names ->
            let d = domain_of dom in
            mapper_of_tuply names d in
    let lists = List.map
        mapper tuply_bounds in
    let bound_lists, def_lists =
        List.split lists in
    let bounds = List.concat bound_lists in
    let defs = List.concat def_lists in
    (* insert a `LET...IN`,
    needed to represent tuple
    declarations, for example:

    [<<x, y>> \in S,  r, w \in Q |->
        x + y - r - w]

    is represented with `bs` containing
    the declarations
    `fcnbnd#x \in S`, `r \in Q`,
    `w \in Ditto`, and
    `e` the expression

        LET
            x == fcnbnd#x[1]
            y == fcnbnd#x[2]
        IN
            x + y - r - w
    *)
    match defs with
    | [] -> (value, bounds)
    | _ ->
        let value = make_let
            defs value in
        (value, bounds)


let make_setof_from_tuply
        (elem: expr)
        (tuply_bounds: tuply_bounds):
            expr =
    assert_nonempty tuply_bounds "bounds";
    let elem, bounds = make_let_for_setof_from_tuple
        tuply_bounds elem true in
    SetOf (elem, bounds) @@ nowhere


let make_fcn_from_tuply
        (tuply_bounds: tuply_bounds)
        (value: expr):
            expr =
    (* Insert a `LET...IN` for representing
    bound identifiers described by bounded tuples in
    the source.

    A function constructor is represented with `Fcn`,
    which takes `bounds` as first argument.
    `bounds` represents a list of
    bound identifiers (constants here).

    So the tuples need to be converted to
    individual identifier bounds.
    This is done by introducing intermediate
    definitions in a `LET...IN`.
    Each bounded tuple (like `<<x, y>> \in S`)
    is replaced by a fresh identifier of the form:

        fcnbnd#first_name

    where "first_name" results from using the
    first identifier that occurs within the tuple.
    For example, `<<x, y>>` is replaced by

        fcnbnd#x

    The fresh identifier is used inside
    the `LET...IN` for defining each
    of the identifiers that occurred
    within the tuple. For example,
    `[<<x, y>> \in S |-> ...]` becomes:

        [fcnbnd#x \in S:
            LET
                x == fcnbnd#x[1]
                y == fcnbnd#x[2]
            IN
                ...]

    The hashmark is used within the identifier
    fcnbnd#... to ensure that
    the fresh identifier is different from
    all other identifiers in the
    current context, without the need to
    inspect the context (which is
    not available while parsing).
    The syntax of TLA+ ensures this,
    because no identifier in TLA+ source
    can contain a hashmark.

    In each function constructor,
    the first identifier from the tuple
    (like "x" above) is unique,
    because the TLA+ syntax ensures that
    each identifier is unique within its context.
    Therefore, each bounded tuple within
    a function constructor will be replaced
    by a unique fresh identifier
    (unique within that context and
    the extensions of that context.
    *)
    assert_nonempty tuply_bounds "bounds";
    let value, bounds = make_let_for_setof_from_tuple
        tuply_bounds value false in
    Fcn (bounds, value) @@ nowhere


class tuply_declaration_expander =
    object (self: 'self)
    inherit [unit] Visit.map_concrete as super

    method expr scx oe =
        let e = super#expr scx oe in
        match e.core with
        | QuantTuply (qfr, bs, pred) ->
            make_quant_from_tuply
                qfr bs pred $$ e
        | ChooseTuply (names, optdom, pred) ->
            make_choose_from_tuply
                names optdom pred $$ e
        | SetStTuply (names, dom, pred) ->
            make_setst_from_tuply
                names dom pred $$ e
        | SetOfTuply (elem, bs) ->
            make_setof_from_tuply elem bs $$ e
        | FcnTuply (bs, value) ->
            make_fcn_from_tuply bs value $$ e
        | _ -> e
end


class no_tuply_declarations_checker =
    object (self: 'self)
    inherit [unit] Visit.iter_concrete as super

    method expr scx oe =
        super#expr scx oe;
        match oe.core with
        | QuantTuply _
        | ChooseTuply _
        | SetStTuply _
        | SetOfTuply _
        | FcnTuply _ ->
            assert false
        | _ -> ()
end


let assert_no_tuply (e: expr) =
    let visitor = new no_tuply_declarations_checker in
    let scx = ((), Deque.empty) in
    visitor#expr scx e


let expand_tuply_declarations (e: expr): expr =
    (* Return abstract tree from concrete tree `e`.

    A concrete syntax tree includes nodes that
    represent tuply declarations, i.e.,
    TLA+ declarations of the form <<x, ..., y>>.

    An abstract syntax tree includes declarations
    of only identifiers (i.e., no tuple syntax
    appears in declarations in an abstract syntax
    tree).

    The translation implemented by this function
    is described in the book "Specifying systems".
    *)
    let visitor = new tuply_declaration_expander in
    let scx = ((), Deque.empty) in
    let e = visitor#expr scx e in
    assert_no_tuply e;
    e


let is_unbounded = function
    | (_, _, No_domain) -> true
    | _ -> false


let exists_unbounded bounds =
    List.exists is_unbounded bounds


let collect_domains_of (bounds: bounds): expr list =
    let mapper = function
        | (_, _, Domain dom) -> dom
        | _ -> assert false in
    List.map mapper bounds


(* TODO: confirm once more that it is sound to
rewrite recursive function definitions only later,
i.e., after expanding tuply declarations.
*)
let tuplify_fcn_signature_params
        (bounds: bounds)
        (value: expr):
            expr =
    assert_nonempty bounds "bounds";
    if (exists_unbounded bounds) then
        failwith "unexpected unbounded constant";
    let bounds = unditto bounds in
    (* tupling *)
    let name = name_of_bound (List.hd bounds) in
    let fresh_hint = make_fresh_name "tupling" name in
    let fresh_bound =
        let components = collect_domains_of bounds in
        let cart_dom = make_product components in
        (fresh_hint, Constant, Domain cart_dom) in
    let value = make_letin_from_tuply
        fresh_hint (names_of_bounds bounds) value in
    make_fcn [fresh_bound] value


class fcn_tuplifier =
    object (self: 'self)
    inherit [unit] Visit.map_concrete as super

    method expr scx oe =
        let expr = super#expr scx oe in
        match expr.core with
        | Fcn (bounds, value) -> begin
            match bounds with
            | [] -> assert false
            | [_] -> expr
            | _ ->
                tuplify_fcn_signature_params
                    bounds value
                    $$ expr
            end
        | FcnApp (fcn, args) -> begin
            match args with
            | [] -> assert false
            | [_] -> expr
            | _ ->
                let arg = make_tuple args in
                make_fcn_app fcn arg
                    $$ expr
            end
        | _ -> expr
end


let tuplify_functions (e: expr): expr =
    (* Tuplify function signatures and applications.

    For example:

    - `[x \in A, y \in B |-> x + y]`
      becomes (modulo naming of identifiers)
      `[xy \in A \X B |-> xy[1] + xy[2]]`

    - `f[x, y, z]` becomes `f[<<x, y, z>>]`

    The motivation for tuplification is both
    that this is what this syntax stands for,
    and that backends do not support specialized
    reasoning about comma-separated declarations
    in function signatures, nor comma-separated
    arguments in function application.
    *)
    let visitor = new fcn_tuplifier in
    let scx = ((), Deque.empty) in
    visitor#expr scx e
