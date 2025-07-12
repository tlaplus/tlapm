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

let leaf (name : string) : field_or_node = Node {name; children = []}
  
let field_leaf (field_name : string) (name : string) : field_or_node =
  Field (field_name, {name; children = []})
  
let node_list_map (f : 'a -> ts_node) (ls : 'a list) : field_or_node list =
  List.map (fun e -> Node e) (List.map f ls)

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
  | "Nat" -> {name = "nat_number_set"; children = []}
  | "Int" -> {name = "int_number_set"; children = []}
  | "Real" -> {name = "real_number_set"; children = []}
  | "FALSE" -> {name = "boolean"; children = []}
  | "TRUE" -> {name = "boolean"; children = []}
  | "STRING" -> {name = "string_set"; children = []}
  | _ -> {
    name = (match if_id with | Declaration -> "identifier" | Reference -> "identifier_ref");
    children = []
  }

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

let translate_operator_declaration (name : string) (arity : int) : field_or_node list =
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
  | Shape_op arity -> Node {
    name = "operator_declaration";
    children = translate_operator_declaration name.core arity;
  }

let translate_variable_decl (_ : Util.hint) : field_or_node =
  leaf "identifier"

let translate_recursive_decl ((_hint, _shape) : (Util.hint * Expr.T.shape)) : field_or_node =
  leaf "recursive_ph"
  
let translate_operator_parameter ((name, shape) : Util.hint * Expr.T.shape) : field_or_node =
  match shape with
  | Shape_expr -> field_leaf "parameter" "identifier"
  | Shape_op arity -> Field ("parameter", {
    name = "operator_declaration";
    children = translate_operator_declaration name.core arity;
  })

let translate_number (_number : string) (decimal : string) : ts_node =
  if String.empty = decimal
  then {name = "nat_number"; children = []}
  else {name = "real_number"; children = []}

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
and translate_quantifier_bound ((_hint, _, bound_domain) : Expr.T.bound) : field_or_node =
  match bound_domain with
  | Domain expr -> Node {
    name = "quantifier_bound";
    children = [
      field_leaf "intro" "identifier";
      leaf "set_in";
      Field ("set", translate_expr expr)
    ]
  }
  | _ -> failwith "Invalid function domain"

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

(** Top-level translation method for all expression types. *)
and translate_expr (expr : Expr.T.expr) : ts_node =
  match expr.core with
  | Num (number, decimal) -> translate_number number decimal
  | String str -> translate_string str
  | Opaque id -> as_specific_name Reference id
  | Internal internal -> internal |> builtin_to_op |> op_to_node Reference
  | List (bullet, juncts) -> translate_jlist bullet juncts
  | Apply (callee, args) -> translate_bound_op callee args
  | Parens (expr, pform) -> translate_parentheses expr pform
  | Lambda (params, expr) -> translate_lambda params expr
  | SetEnum expr_ls -> {name = "finite_set_literal"; children = node_list_map translate_expr expr_ls }
  | Tuple expr_ls -> {
    name = "tuple_literal";
    children = [leaf "langle_bracket"] @ (node_list_map translate_expr expr_ls) @ [leaf "rangle_bracket"]
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
  | _ -> {name = "expr_ph"; children = []}

let translate_operator_definition (defn : Expr.T.defn) : ts_node =
  match defn.core with
  | Recursive (_name, _shape) -> {name = "recursive_ph"; children = []}
  | Operator (name, expr) -> (
    match expr.core with
    (* Operators with parameters are represented by a LAMBDA expression. *)
    | Lambda (params, expr) -> {
      name = "operator_definition";
      children = List.flatten [
        [field_leaf "name" "identifier"];
        List.map translate_operator_parameter params;
        [leaf "def_eq"];
        [Field ("definition", (translate_expr expr))]
      ]
    }
    | Fcn (bounds, expr) -> {
      name = "function_definition";
      children = List.flatten [
        [field_leaf "name" "identifier"];
        List.map translate_quantifier_bound bounds;
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

let translate_assumption (name : Util.hint option) (expr : Expr.T.expr) : field_or_node list =
  List.flatten [
    if Option.is_some name then [field_leaf "name" "identifier"; leaf "def_eq"] else [];
    [Node (translate_expr expr)]
  ]

let translate_theorem (name : Util.hint option) (sequent : Expr.T.sequent) (_level : int) (_proof1 : Proof.T.proof) (_proof2 : Proof.T.proof) (_summary : Module.T.summary) : field_or_node list =
  List.flatten [
    if Option.is_some name then [field_leaf "name" "identifier"; leaf "def_eq"] else [];
    [Field ("statement", translate_expr sequent.active)]
  ]

let rec translate_module (tree : Module.T.mule) : ts_node = {
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
