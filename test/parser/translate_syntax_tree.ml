(** This file contains functionality for translating TLAPM's syntax tree
    format into the common TLA+ syntax corpus format, for comparison of
    expected with actual parse trees for a given parse input.
*)

open Sexplib;;
open Tlapm_lib;;

type field_or_node =
  | Field of string * ts_node
  | Node of ts_node
and ts_node = {
  name : string;
  children : field_or_node list;
}

let leaf_node (name : string) : ts_node = {
  name;
  children = []
}

let leaf (name : string) : field_or_node = Node (leaf_node name)

let field_leaf (field_name : string) (name : string) : field_or_node =
  Field (field_name, leaf_node name)

let node_list (ls : ts_node list) : field_or_node list =
  List.map (fun e -> Node e) ls

let node_list_map (f : 'a -> ts_node) (ls : 'a list) : field_or_node list =
  node_list (List.map f ls)

let field_list (field : string) (ls : 'a list) : field_or_node list =
  List.map (fun e -> Field (field, e)) ls

let field_list_map (field : string) (f : 'a -> ts_node) (ls : 'a list) : field_or_node list =
  field_list field (List.map f ls)

let rec ts_node_to_sexpr (node : ts_node) : Sexp.t =
  let flatten_child (child : field_or_node) : Sexp.t list =
    match child with
    | Field (name, node) -> [
        Atom (name ^ ":");
        ts_node_to_sexpr node
      ]
    | Node (node) -> [ts_node_to_sexpr node]
  in
  Sexp.(List
    (Atom node.name ::
      List.flatten (List.map flatten_child node.children)
    )
  )

let rec repeat (count : int) (elem : 't) : 't list =
  if count = 0 then [] else elem :: (repeat (count - 1) elem)

type operator =
  | Prefix of string
  | Infix of string
  | Postfix of string
  | Named of string

type decl_or_ref =
  | Declaration
  | Reference

let as_specific_name (if_id : decl_or_ref) (id : string) : ts_node =
  match id with
  | "Nat" -> leaf_node "nat_number_set"
  | "Int" -> leaf_node "int_number_set"
  | "Real" -> leaf_node "real_number_set"
  | "FALSE" -> leaf_node "boolean"
  | "TRUE" -> leaf_node "boolean"
  | "STRING" -> leaf_node "string_set"
  | _ -> leaf_node (match if_id with | Declaration -> "identifier" | Reference -> "identifier_ref")

(** The standardized test corpus requires counting escaped strings (for syntax
    highlighting reasons) so we do a foldl over the characters of the string
    determining whether each character was preceded by a backslash, counting
    up the number of escaped characters in the string.
*)
let translate_string (str : string) : ts_node = {
  name = "string";
  children =
    let (_, escape_count) = String.fold_left (
      fun (is_escaped, acc) c ->
        match is_escaped, c with
        | (true, 't') -> (false, acc + 1)
        | (true, 'n') -> (false, acc + 1)
        | (true, 'r') -> (false, acc + 1)
        | (true, 'f') -> (false, acc + 1)
        | (true, '*') -> (false, acc + 1)
        | (true, '"') -> (false, acc + 1)
        | (true, '\\') -> (false, acc + 1)
        | (_, '\\') -> (true, acc)
        | _ -> (false, acc)
      ) (false, 0) str in
    repeat escape_count (leaf "escape_char")
}

let op_to_node (if_id : decl_or_ref) (op : operator) : ts_node =
  match op with
  | Prefix symbol -> {name = "prefix_op_symbol"; children = [leaf symbol]}
  | Infix symbol -> {name = "infix_op_symbol"; children = [leaf symbol]}
  | Postfix symbol -> {name = "postfix_op_symbol"; children = [leaf symbol]}
  | Named name -> as_specific_name if_id name

let str_to_op (op_str : string) : operator =
  match op_str with
  | "ENABLED" -> Prefix "enabled"
  | "DOMAIN" -> Prefix "domain"
  | "SUBSET" -> Prefix "powerset"
  | "UNCHANGED" -> Prefix "unchanged"
  | "UNION" -> Prefix "union"
  | "[]" -> Prefix "always"
  | "<>" -> Prefix "eventually"
  | "~" -> Prefix "lnot"
  | "-." -> Prefix "negative"
  | "-" -> Infix "minus"
  | "+" -> Infix "plus"
  | "*" -> Infix "mul"
  | "/" -> Infix "slash"
  | ":>" -> Infix "map_to"
  | "&" -> Infix "amp"
  | ":=" -> Infix "assign"
  | "::=" -> Infix "bnf_rule"
  | "\\o" -> Infix "circ"
  | "->" -> Infix "map_to"
  | "'" -> Postfix "prime"
  | "^+" -> Postfix "sup_plus"
  | _ -> Named op_str

let as_bound_op (op : Expr.T.expr) : operator =
  match op.core with
  | Opaque name -> Named name
  | _ -> Named "expr_as_bound_op_ph"

let builtin_to_op (builtin : Builtin.builtin) : operator =
  match builtin with
  | TRUE -> Named "TRUE"
  | FALSE -> Named "FALSE"
  | BOOLEAN -> Named "BOOLEAN"
  | STRING -> Named "STRING"
  | SUBSET -> Prefix "powerset"
  | UNION -> Prefix "union"
  | DOMAIN -> Prefix "domain"
  | Neg -> Prefix "lnot"
  | Plus -> Infix "plus"
  | Mem -> Infix "in"
  | Notmem -> Infix "notin"
  | Implies -> Infix "implies"
  | Equiv -> Infix "equiv"
  | Conj -> Infix "land"
  | Disj -> Infix "lor"
  | Eq -> Infix "eq"
  | Neq -> Infix "neq"
  | Setminus -> Infix "setminus"
  | Cap -> Infix "cap"
  | Cup -> Infix "cup"
  | Prime -> Postfix "prime"
  | _ -> failwith "unknown built-in"

let translate_operator_declaration (name : string) (arity : int) : ts_node = {
    name = "operator_declaration";
    children =
    let op = str_to_op name in
    let symbol = op_to_node Declaration op in
    match op with
    | Prefix _ -> [
      Field ("name", symbol);
      leaf "placeholder"
    ]
    | Infix _ -> [
      leaf "placeholder";
      Field ("name", symbol);
      leaf "placeholder"
    ]
    | Postfix _ -> [
      leaf "placeholder";
      Field ("name", symbol);
    ]
    | Named _ -> (Field ("name", symbol)) :: (repeat arity (field_leaf "parameter" "placeholder"))
  }

let translate_extends (tree : Util.hints) : field_or_node list =
  match tree with
  | [] -> []
  | _ -> [(Node {
    name = "extends";
    children = (List.map (fun _ -> leaf "identifier_ref") tree)
  })]

let translate_constant_decl ((name, shape) : (Util.hint * Expr.T.shape)) : field_or_node =
  match shape with
  | Shape_expr -> leaf "identifier"
  | Shape_op arity -> Node (translate_operator_declaration name.core arity)

let translate_variable_decl (_ : Util.hint) : field_or_node =
  leaf "identifier"

let translate_recursive_decl ((name, shape) : (Util.hint * Expr.T.shape)) : field_or_node =
  match shape with
  | Shape_expr -> field_leaf "name" "identifier"
  | Shape_op arity -> Node (translate_operator_declaration name.core arity)

let translate_operator_parameter ((name, shape) : Util.hint * Expr.T.shape) : field_or_node =
  match shape with
  | Shape_expr -> field_leaf "parameter" "identifier"
  | Shape_op arity -> Field ("parameter", translate_operator_declaration name.core arity)

let translate_number (_number : string) (decimal : string) : ts_node =
  if String.empty = decimal
  then leaf_node "nat_number"
  else leaf_node "real_number"

(** For expressions like \A x, y \in Nat : f(x, y), the first x will have
    bound_domain variant Domain with an associated expression corresponding
    to the set being enumerated, and the second variable y will have
    bound_domain variant Ditto without any associated domain information;
    this function regroups these into a list of identifiers underneath a
    single set expression. It is different from the unditto function which
    clones the set expression into the y variable bound_domain.
*)
let group_bounds (bounds : Expr.T.bound list) : (ts_node list * Expr.T.expr) list =
  let (final_groups, _) = List.fold_right (fun ((_, _, domain) : Expr.T.bound) ((groups, partial_group) : ((ts_node list * Expr.T.expr) list) * ts_node list) ->
    match domain with
    | Ditto -> (groups, leaf_node "identifier" :: partial_group)
    | Domain expr -> ((leaf_node "identifier" :: partial_group, expr) :: groups, [])
    | No_domain -> failwith "Encountered unbounded domain when grouping bounds"
  ) bounds ([], [])
  in final_groups

let group_tuple_bounds (bounds : Expr.T.tuply_bound list) : (ts_node list * Expr.T.expr) list =
  let (final_groups, _) = List.fold_right (fun ((names, domain) : Expr.T.tuply_bound) ((groups, partial_group) : ((ts_node list * Expr.T.expr) list) * ts_node list) ->
    match names, domain with
    | (Bound_name _, Ditto) -> (groups, leaf_node "identifier" :: partial_group)
    | (Bound_name _, Domain expr) -> ((leaf_node "identifier" :: partial_group, expr) :: groups, [])
    | (Bound_names names, Domain expr) -> (
        let tuple = {
          name = "tuple_of_identifiers";
          children = List.flatten [
            [leaf "langle_bracket"];
            List.map (fun _ -> leaf "identifier") names;
            [leaf "rangle_bracket"];
          ]
        } in ([tuple], expr) :: groups, [])
    | (Bound_names _, Ditto) -> failwith "Combination of multiple bound names and ditto bound is never used"
    | (_, No_domain) -> failwith "Tuple quantifiers must have a domain; this should not be representable"
  ) bounds ([], [])
  in final_groups

(** Translates the substitution component of INSTANCE statements like s <- expr *)
let rec translate_substitution ((hint, expr) : (Util.hint * Expr.T.expr)) : field_or_node =
  Node {
    name = "substitution";
    children = [
      Node (hint.core |> str_to_op |> op_to_node Reference);
      leaf "gets";
      Node (translate_expr expr)
    ]
  }

(** Translates statements like INSTANCE M WITH s1 <- e1, s2 <- e2 *)
and translate_instance (instance : Expr.T.instance) : ts_node = {
  name = "instance";
  children = List.flatten [
    [leaf "identifier_ref"];
    List.map translate_substitution instance.inst_sub
  ]
}

and translate_cross_product (exprs : Expr.T.expr list) : ts_node =
  match exprs with
  | [] -> failwith "Empty cross product"
  | hd :: tl -> List.fold_left (
    fun lhs rhs -> {
      name = "bound_infix_op";
      children = [
        Field ("lhs", lhs);
        field_leaf "symbol" "times";
        Field ("rhs", translate_expr rhs);
      ]
    }) (translate_expr hd) tl

and translate_subexpression (expr : Expr.T.expr) (selectors : Expr.T.sel list) : ts_node =
  (*let _ =match expr.core with
  | Opaque s -> failwith s;
  | _ -> failwith "Something else"
in*)
  let translate_final_selector (selector : Expr.T.sel) : ts_node =
    match selector with
    | Sel_lab (name, args) ->
      if List.is_empty args then as_specific_name Reference name else {
        name = "bound_op";
        children = List.flatten [
          [field_leaf "name" "identifier_ref"];
          List.map (fun arg -> Field ("parameter", (translate_expr arg))) args
        ]
      }
    | _ -> failwith "final_selector"
  in {
    name = "prefixed_op";
    children = [
      Field ("prefix", {
        name = "subexpr_prefix";
        children = [Node {
          name = "subexpr_component";
          children = [Node (translate_expr expr)]
        }]
      });
      let last (ls : 'a list) : 'a = List.nth ls ((List.length ls) - 1) in
      Field ("op", translate_final_selector (last selectors));
    ]
  }

(** Translate conjunction & disjunction lists like
  /\ e1
  /\ e2
  /\ e3
*)
and translate_jlist (bullet : Expr.T.bullet) (juncts : Expr.T.expr list) : ts_node =
  let jtype = match bullet with | And -> "conj" | Or -> "disj" | _ -> failwith "jlist"
  in {
    name = jtype ^ "_list";
    children = List.map (fun expr -> Node {
      name = jtype ^ "_item";
      children = [leaf ("bullet_" ^ jtype); Node (translate_expr expr)]
    }) juncts
  }

and translate_quantifier_bound ((names, domain) : (ts_node list * Expr.T.expr)) : ts_node = {
    name = "quantifier_bound";
    children = List.flatten [
      field_list "intro" names;
      [leaf "set_in"];
      [Field ("set", translate_expr domain)]
    ]
  }

and translate_quantifier_bounds (bounds : Expr.T.bound list) : ts_node list =
  bounds |> group_bounds |> List.map translate_quantifier_bound

and translate_tuple_quantifier_bounds (bounds : Expr.T.tuply_bound list) : ts_node list =
  bounds |> group_tuple_bounds |> List.map translate_quantifier_bound

and translate_case_arm (index : int) ((pred, expr) : Expr.T.expr * Expr.T.expr) : field_or_node list =
  let case = Node {
    name = "case_arm";
    children = [
      Node (translate_expr pred);
      leaf "case_arrow";
      Node (translate_expr expr);
    ]
  } in match index with
  | 0 -> [case]
  | _ -> [leaf "case_box"; case]

and translate_default_arm (default : Expr.T.expr option) : field_or_node list =
  match default with
  | None -> []
  | Some expr -> [
    leaf "case_box";
    Node {
      name = "other_arm";
      children = [
        leaf "case_arrow";
        Node (translate_expr expr)
      ]
    }
  ]

and translate_case (cases : (Expr.T.expr * Expr.T.expr) list) (default : Expr.T.expr option) : ts_node = {
  name = "case";
  children = List.flatten [
    List.mapi translate_case_arm cases |> List.flatten;
    translate_default_arm default
  ]
}

and translate_bound_op (callee : Expr.T.expr) (args : Expr.T.expr list) : ts_node =
  let op : operator =
    match callee.core with
    | Opaque op -> str_to_op op
    | Internal builtin -> builtin_to_op builtin
    | _ -> failwith "bound_op callee"
  in match op with
  | Prefix op -> {
    name = "bound_prefix_op";
    children = [
      field_leaf "symbol" op;
      Field ("rhs", translate_expr (List.hd args))
    ]
  }
  | Infix op -> {
    name = "bound_infix_op";
    children = [
      Field ("lhs", translate_expr (List.nth args 0));
      field_leaf "symbol" op;
      Field ("rhs", translate_expr (List.nth args 1));
    ]
  }
  | Postfix op -> {
    name = "bound_postfix_op";
    children = [
      Field ("lhs", translate_expr (List.hd args));
      field_leaf "symbol" op;
    ]
  }
  | Named _ -> {
    name = "bound_op";
    children = List.flatten [
      [field_leaf "name" "identifier_ref"];
      List.map (fun arg -> Field ("parameter", (translate_expr arg))) args
    ]
  }

and translate_lambda (params : (Util.hint * Expr.T.shape) list) (expr : Expr.T.expr) : ts_node = {
  name = "lambda";
  children = List.flatten [
    List.map (fun _ -> leaf "identifier") params;
    [Node (translate_expr expr)]
  ]
}

and translate_parentheses (expr : Expr.T.expr) (pform : Expr.T.pform) : ts_node =
  match pform.core with
  | Syntax -> {
    name = "parentheses";
    children = [Node (translate_expr expr)]
  }
  | Nlabel (_, params) -> {
    name = "label";
    children = List.flatten [
      [field_leaf "name" "identifier"];
      List.map (fun _ -> field_leaf "parameter" "identifier_ref") params;
      [leaf "label_as"];
      [Field ("expression", translate_expr expr)]
    ]
  }
  | Xlabel _ -> failwith "parens_xlabel"

and translate_set_filter (_name : Util.hint) (set : Expr.T.expr) (filter : Expr.T.expr) : ts_node = {
  name = "set_filter";
  children = [
    Field ("generator", {
      name = "quantifier_bound";
      children = [
        field_leaf "intro" "identifier";
        leaf "set_in";
        Field ("set", translate_expr set);
      ]
    });
    Field ("filter", translate_expr filter)
  ]
}

and translate_tuple_of_identifiers (names : Util.hint list) : ts_node = {
    name = "tuple_of_identifiers";
    children = List.flatten [
      [leaf "langle_bracket"];
      List.map (fun _ -> leaf "identifier") names;
      [leaf "rangle_bracket"];
    ]
  }

and translate_tuple_set_filter (names : Util.hint list) (set : Expr.T.expr) (filter : Expr.T.expr) : ts_node = {
  name = "set_filter";
  children = [
    Field ("generator", {
      name = "quantifier_bound";
      children = [
        Field ("intro", translate_tuple_of_identifiers names);
        leaf "set_in";
        Field ("set", translate_expr set)
      ]
    });
    Field ("filter", translate_expr filter);
  ]
}

and translate_set_map (map : Expr.T.expr) (bounds : Expr.T.bound list) : ts_node = {
  name = "set_map";
  children = List.flatten [
    [Field ("map", translate_expr map)];
    field_list "generator" (translate_quantifier_bounds bounds);
  ]
}

and translate_tuple_set_map (map : Expr.T.expr) (bounds : Expr.T.tuply_bound list) : ts_node =
  let bounds = Expr.T.unditto_tuply bounds in {
  name = "set_map";
  children = List.flatten [
    [Field ("map", translate_expr map)];
    bounds |> translate_tuple_quantifier_bounds |> field_list "generator";
  ]
}

and translate_quantification (quantifier : Expr.T.quantifier) (bounds : Expr.T.bound list) (body : Expr.T.expr) : ts_node =
  let is_bound (bounds : Expr.T.bound list) : bool =
    List.for_all (fun (_, _, domain) -> match (domain : Expr.T.bound_domain) with | No_domain -> false | _ -> true ) bounds
  in if is_bound bounds then {
    name = "bounded_quantification";
    children = List.flatten [
      [field_leaf "quantifier" (match quantifier with | Forall -> "forall" | Exists -> "exists")];
      bounds |> translate_quantifier_bounds |> field_list "bound";
      [Field ("expression", translate_expr body)];
    ]
  } else {
    name = "unbounded_quantification";
    children = List.flatten [
      [field_leaf "quantifier" (match quantifier with | Forall -> "forall" | Exists -> "exists")];
      List.map (fun _ -> field_leaf "intro" "identifier") bounds;
      [Field ("expression", translate_expr body)];
    ]
  }

and translate_tuple_bounded_quantification (quantifier : Expr.T.quantifier) (bounds : Expr.T.tuply_bound list) (body : Expr.T.expr) : ts_node = {
  name = "bounded_quantification";
  children = List.flatten [
    [field_leaf "quantifier" (match quantifier with | Forall -> "forall" | Exists -> "exists")];
    bounds |> translate_tuple_quantifier_bounds |> field_list "bound";
    [Field ("expression", translate_expr body)];
  ]
}

and translate_temporal_quantification (quantifier : Expr.T.quantifier) (names : Util.hints) (body : Expr.T.expr) : ts_node = {
  name = "unbounded_quantification";
  children = List.flatten [
    [field_leaf "quantifier" (match quantifier with | Forall -> "temporal_forall" | Exists -> "temporal_exists")];
    List.map (fun _ -> field_leaf "intro" "identifier") names;
    [Field ("expression", translate_expr body)];
  ]
}

and translate_choose (_name : Util.hint) (set : Expr.T.expr option) (body : Expr.T.expr) : ts_node = {
  name = "choose";
  children = List.flatten [
    [field_leaf "intro" "identifier"];
    (match set with | Some expr -> [leaf "set_in"; Field ("set", translate_expr expr)] | None -> []);
    [Field ("expression", translate_expr body)]
  ]
}

and translate_tuple_choose (names : Util.hint list) (set : Expr.T.expr option) (body : Expr.T.expr) : ts_node = {
  name = "choose";
  children = List.flatten [
    [Field ("intro", translate_tuple_of_identifiers names)];
    (match set with | Some expr -> [leaf "set_in"; Field ("set", translate_expr expr)] | None -> []);
    [Field ("expression", translate_expr body)]
  ]
}

and translate_step_expr (mode : Expr.T.modal_op) (expr : Expr.T.expr) (sub : Expr.T.expr) : ts_node =
  match mode with
  | Box -> {
    name = "step_expr_or_stutter";
    children = [Node (translate_expr expr); Node (translate_expr sub)]
  }
  | Dia -> {
    name = "step_expr_no_stutter";
    children = [
      leaf "langle_bracket";
      Node (translate_expr expr);
      leaf "rangle_bracket_sub";
      Node (translate_expr sub);
    ]
  }

and translate_except (fn : Expr.T.expr) (excepts : (Expr.T.expoint list * Expr.T.expr) list) =
  let translate_except_update_specifier (except_specifier : Expr.T.expoint) =
    match except_specifier with
    | Except_dot _record_field_name -> {
      name = "except_update_record_field";
      children = [leaf "identifier_ref"]
    }
    | Except_apply expr -> {
      name =  "except_update_fn_appl";
      children = [Node (translate_expr expr)]
    }
  in let translate_except_update ((except_specifiers, new_val) : Expr.T.expoint list * Expr.T.expr) = {
    name = "except_update";
    children = [
      Field ("update_specifier", {
        name = "except_update_specifier";
        children = node_list_map translate_except_update_specifier except_specifiers
      });
      Field ("new_val", translate_expr new_val)
    ]
  } in {
    name = "except";
    children = List.flatten [
      [Field ("expr_to_update", translate_expr fn)];
      node_list_map translate_except_update excepts
    ]
  }

(** Top-level translation method for all expression types. *)
and translate_expr (expr : Expr.T.expr) : ts_node =
  match expr.core with
  | Num (number, decimal) -> translate_number number decimal
  | String str -> translate_string str
  | Opaque id -> as_specific_name Reference id
  | Internal internal -> internal |> builtin_to_op |> op_to_node Reference
  | List (bullet, juncts) -> translate_jlist bullet juncts
  | Product exprs -> translate_cross_product exprs
  | Apply (callee, args) -> translate_bound_op callee args
  | Parens (expr, pform) -> translate_parentheses expr pform
  | Lambda (params, expr) -> translate_lambda params expr
  | SetEnum exprs -> {name = "finite_set_literal"; children = node_list_map translate_expr exprs }
  | SetSt (name, set, filter) -> translate_set_filter name set filter
  | SetStTuply (names, set, filter) -> translate_tuple_set_filter names set filter
  | SetOf (map, bounds) -> translate_set_map map bounds
  | SetOfTuply (map, bounds) -> translate_tuple_set_map map bounds
  | Quant (quantifier, bounds, expr) -> translate_quantification quantifier bounds expr
  | QuantTuply (quantifier, bounds, expr) -> translate_tuple_bounded_quantification quantifier bounds expr
  | Tquant (quantifier, hints, expr) -> translate_temporal_quantification quantifier hints expr
  | Choose (name, set, expr) -> translate_choose name set expr
  | ChooseTuply (names, set, expr) -> translate_tuple_choose names set expr
  | Except (fn, excepts) -> translate_except fn excepts
  | At (_from_except) -> leaf_node "prev_func_val"
  | Sub (mode, expr, sub) -> translate_step_expr mode expr sub
  | Tsub (mode, expr, sub) -> {
    name = "bound_prefix_op";
    children = [
      Field ("symbol", (match mode with | Box -> leaf_node "always" | Dia -> leaf_node "eventually"));
      Field ("rhs", translate_step_expr mode expr sub);
    ];
  }
  | Fair (_op, sub, expr) -> {
    name = "fairness";
    children = [
      Node (translate_expr sub);
      Node (translate_expr expr);
    ]
  }
  | Arrow (domain, range) -> {
    name = "set_of_functions";
    children = [
      Node (translate_expr domain);
      leaf "maps_to";
      Node (translate_expr range);
    ]
  }
  | Fcn (bounds, expr) -> {
    name = "function_literal";
    children = List.flatten [
      bounds |> translate_quantifier_bounds |> node_list;
      [leaf "all_map_to"];
      [Node (translate_expr expr)]
    ]
  }
  | FcnTuply (bounds, expr) -> {
    name = "function_literal";
    children = List.flatten [
      bounds |> translate_tuple_quantifier_bounds |> node_list;
      [leaf "all_map_to"];
      [Node (translate_expr expr)]
    ]
  }
  | FcnApp (fn_expr, arg_exprs) -> {
    name = "function_evaluation";
    children = List.flatten [
      [Node (translate_expr fn_expr)];
      node_list_map translate_expr arg_exprs
    ]
  }
  | Let (definitions, expr) -> {
    name = "let_in";
    children = List.flatten [
      field_list_map "definitions" translate_operator_definition definitions;
      [Field ("expression", (translate_expr expr))]
    ]
  }
  | Tuple expr_ls -> {
    name = "tuple_literal";
    children = [leaf "langle_bracket"] @ (node_list_map translate_expr expr_ls) @ [leaf "rangle_bracket"]
  }
  | Rect fields -> {
    name = "set_of_records";
    children = List.flatten (List.map (fun (_, expr) -> [leaf "identifier"; Node (translate_expr expr)]) fields)
  }
  | Record fields -> {
    name = "record_literal";
    children = List.flatten (List.map (fun (_, expr) -> [leaf "identifier"; leaf "all_map_to"; Node (translate_expr expr)]) fields)
  }
  | Dot (expr, _) -> {
    name = "record_value";
    children = [Node (translate_expr expr); leaf "identifier_ref"]
  }
  | If (i, t, e) -> {
    name = "if_then_else";
    children = [
      Field ("if", translate_expr i);
      Field ("then", translate_expr t);
      Field ("else", translate_expr e);
    ]
  }
  | Case (cases, other) -> translate_case cases other
  | Bang (expr, selectors) -> translate_subexpression expr selectors
  | _ -> leaf_node "expr_ph"

and translate_operator_definition (defn : Expr.T.defn) : ts_node =
  match defn.core with
  | Recursive (_name, _shape) -> leaf_node "recursive_ph"
  | Operator (name, expr) -> (
    match expr.core with
    (* Operators with parameters are represented by a LAMBDA expression. *)
    | Lambda (params, expr) -> {
      name = "operator_definition";
      children = List.flatten [
        [Field ("name", name.core |> str_to_op |> op_to_node Declaration)];
        List.map translate_operator_parameter params;
        [leaf "def_eq"];
        [Field ("definition", (translate_expr expr))]
      ]
    }
    (* Function definitions are represented by a function literal. *)
    | Fcn (bounds, expr) -> {
      name = "function_definition";
      children = List.flatten [
        [field_leaf "name" "identifier"];
        bounds |> translate_quantifier_bounds |> node_list;
        [leaf "def_eq"];
        [Field ("definition", translate_expr expr)]
      ]
    }
    (* Operators without parameters are represented by a non-LAMBDA expression. *)
    | _ -> {
      name = "operator_definition";
      children = [
        Field ("name", (as_specific_name Declaration name.core));
        leaf "def_eq";
        Field ("definition", translate_expr expr)
      ]
    }
  )
  | Instance (_hint, instance) -> {
    name = "module_definition";
    children = List.flatten [
      [field_leaf "name" "identifier"];
      [leaf "def_eq"];
      [Field ("definition", (translate_instance instance))];
    ]
  }
  | Bpragma _ -> assert false

and translate_assumption (name : Util.hint option) (expr : Expr.T.expr) : field_or_node list =
  List.flatten [
    if Option.is_some name then [field_leaf "name" "identifier"; leaf "def_eq"] else [];
    [Node (translate_expr expr)]
  ]

and translate_theorem (name : Util.hint option) (sequent : Expr.T.sequent) (_level : int) (_proof1 : Proof.T.proof) (_proof2 : Proof.T.proof) (_summary : Module.T.summary) : field_or_node list =
  List.flatten [
    if Option.is_some name then [field_leaf "name" "identifier"; leaf "def_eq"] else [];
    [Field ("statement", translate_expr sequent.active)]
  ]

and translate_module (tree : Module.T.mule) : ts_node = {
  name = "module";
  children = List.flatten [
    [leaf "header_line"];
    [field_leaf "name" "identifier"];
    [leaf "header_line"];
    translate_extends tree.core.extendees;
    List.map translate_unit tree.core.body;
    [leaf "double_line"];
  ]
}

and translate_unit (unit : Module.T.modunit) : field_or_node =
  match unit.core with
  | Constants ls -> Node {
    name = "constant_declaration";
    children = List.map translate_constant_decl ls
  }
  | Variables ls -> Node {
    name = "variable_declaration";
    children = List.map translate_variable_decl ls
  }
  | Recursives ls -> Node {
    name = "recursive_declaration";
    children = List.map translate_recursive_decl ls
  }
  | Definition (defn, _visibility, _wheredef, export) -> (
    match export with
    | Local -> Node {
      name = "local_definition";
      children = [Node (translate_operator_definition defn)]
    }
    | Export -> Node (translate_operator_definition defn)
  )
  | Axiom (hint, expr) -> Node {
    name = "assumption";
    children = translate_assumption hint expr
  }
  | Theorem (hint, sequent, level, proof1, proof2, summary) -> Node {
    name = "theorem";
    children = translate_theorem hint sequent level proof1 proof2 summary
  }
  | Submod mule -> Node (translate_module mule)
  | Mutate _ -> leaf "mutate_ph"
  | Anoninst (instance, Local) -> Node {
      name = "local_definition";
      children = [Node (translate_instance instance)]
    }
  | Anoninst (instance, Export) -> Node (translate_instance instance)

let translate_tla_source_file (tree : Module.T.mule) : ts_node = {
    name = "source_file";
    children = [Node (translate_module tree)]
  }
