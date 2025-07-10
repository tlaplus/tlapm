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
  | Named

let as_operator (op_str : string) (arity : int) : operator =
  match op_str, arity with
  | ("ENABLED", 1) -> Prefix "enabled"
  | ("DOMAIN", 1) -> Prefix "domain"
  | ("SUBSET", 1) -> Prefix "powerset"
  | ("-", 1) -> Prefix "negative"
  | ("-.", 1) -> Prefix "negative"
  | ("-", 2) -> Infix "minus"
  | ("+", 2) -> Infix "plus"
  | ("'", 1) -> Postfix "prime"
  | ("^+", 1) -> Postfix "sup_plus"
  | _ -> Named

let translate_operator_declaration (name : string) (arity : int) : field_or_node list =
  match as_operator name arity with
  | Prefix symbol -> [
    Field ("name", {name = "prefix_op_symbol"; children = [leaf symbol]});
    leaf "placeholder"
  ]
  | Infix symbol -> [
    leaf "placeholder";
    Field ("name", {name = "infix_op_symbol"; children = [leaf symbol]});
    leaf "placeholder"
  ]
  | Postfix symbol -> [
    leaf "placeholder";
    Field ("name", {name = "postfix_op_symbol"; children = [leaf symbol]});
  ]
  | Named -> (field_leaf "name" "identifier") :: (repeat arity (field_leaf "parameter" "placeholder"))
  
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

(** TODO *)
let translate_variable_decl (_ : Util.hint) : field_or_node =
  leaf "identifier"

(** TODO *)
let translate_recursive_decl ((_hint, _shape) : (Util.hint * Expr.T.shape)) : field_or_node =
  leaf "recursive_ph"
  
let translate_operator_parameter ((_hint, shape) : Util.hint * Expr.T.shape) : field_or_node =
  match shape with
  | Shape_expr -> field_leaf "parameter" "identifier"
  | Shape_op _arity -> leaf "higher_order_param_ph"

let rec translate_substitution ((_hint, expr) : (Util.hint * Expr.T.expr)) : field_or_node =
  Node {
    name = "substitution";
    children = [
      leaf "identifier_ref";
      leaf "gets";
      Node (translate_expr expr)
    ]
  }

and translate_instance (instance : Expr.T.instance) : ts_node = {
  name = "instance";
  children = List.flatten [
    [leaf "identifier_ref"];
    List.map translate_substitution instance.inst_sub
  ]
}

and translate_jlist (bullet : Expr.T.bullet) (juncts : Expr.T.expr list) : ts_node =
  let jtype = match bullet with | And -> "conj" | Or -> "disj" | _ -> failwith "jlist"
  in {
    name = jtype ^ "_list";
    children = List.map (fun expr -> Node {
      name = jtype ^ "_item";
      children = [leaf ("bullet_" ^ jtype); Node (translate_expr expr)]
    }) juncts
  }

and translate_expr (expr : Expr.T.expr) : ts_node =
  match expr.core with
  | Num (_, _) -> {name = "nat_number"; children = []}
  | List (bullet, juncts) -> translate_jlist bullet juncts
  | Apply (_callee, args) -> {
    name = "bound_op";
    children = List.flatten [
      [field_leaf "name" "identifier_ref"];
      List.map (fun arg -> Field ("parameter", (translate_expr arg))) args
    ]
  }
  | _ -> {name = "expr_ph"; children = []}

let translate_operator_definition (defn : Expr.T.defn) : ts_node =
  match defn.core with
  | Recursive (_hint, _shape) -> {name = "recursive_ph"; children = []}
  | Operator (_hint, expr) -> (
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
    (* Operators without parameters are represented by a non-LAMBDA expression. *)
    | _ -> {
      name = "operator_definition";
      children = [
        field_leaf "name" "identifier";
        leaf "def_eq";
        Field ("definition", translate_expr expr)
      ]
    }
  )
  | Instance (_hint, instance) -> {
    name = "module_definition";
    children = List.flatten [
      [field_leaf "name" "identifier_ref"];
      [leaf "def_eq"];
      [leaf "identifier_ref"];
      [Node (translate_instance instance)];
    ]
  }
  | Bpragma _ -> assert false

(** TODO *)
let translate_assumption (_hint : Util.hint option) (_expr : Expr.T.expr) : field_or_node list =
  [leaf "assume_ph"]

(** TODO *)
let translate_theorem (_hint : Util.hint option) (_sequent : Expr.T.sequent) (_level : int) (_proof1 : Proof.T.proof) (_proof2 : Proof.T.proof) (_summary : Module.T.summary) : field_or_node list =
  [leaf "theorem_ph"]

let rec translate_module (tree : Module.T.mule) : ts_node =
  {
    name = "source_file";
    children = [
      Node {
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
