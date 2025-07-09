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
  | ("-", 2) -> Infix "minus"
  | ("+", 2) -> Infix "plus"
  | ("'", 1) -> Postfix "prime"
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
let translate_variable_decl (_decl : Util.hint) : field_or_node =
  leaf "ph"

(** TODO *)
let translate_recursive_decl ((_hint, _shape) : (Util.hint * Expr.T.shape)) : field_or_node =
  leaf "ph"

(** TODO *)
let translate_operator_definition (_defn : Expr.T.defn) (_wheredef : Expr.T.wheredef) (_visibility : Expr.T.visibility) (_export : Expr.T.export) : field_or_node list =
  [leaf "ph"]

(** TODO *)
let translate_assumption (_hint : Util.hint option) (_expr : Expr.T.expr) : field_or_node list =
  [leaf "ph"]

(** TODO *)
let translate_theorem (_hint : Util.hint option) (_sequent : Expr.T.sequent) (_level : int) (_proof1 : Proof.T.proof) (_proof2 : Proof.T.proof) (_summary : Module.T.summary) : field_or_node list =
  [leaf "ph"]

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
  | Definition (defn, wheredef, visibility, export) -> Node {
    name = "operator_definition";
    children = translate_operator_definition defn wheredef visibility export
  }
  | Axiom (hint, expr) -> Node {
    name = "assumption";
    children = translate_assumption hint expr
  }
  | Theorem (hint, sequent, level, proof1, proof2, summary) -> Node {
    name = "theorem";
    children = translate_theorem hint sequent level proof1 proof2 summary
  }
  | Submod mule -> Node (translate_module mule)
  | Mutate _ -> leaf "ph"
  | Anoninst _ -> leaf "ph"
