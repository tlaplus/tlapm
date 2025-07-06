(** This file contains functionality for translating TLAPM's syntax tree
    format into the common TLA+ syntax corpus format, for comparison of
    expected with actual parse trees for a given parse input.
*)

open Sexplib;;

type field_or_node =
  | Field of string * ts_node
  | Node of ts_node
and ts_node = {
  name : string;
  children : field_or_node list;
}

let leaf (name : string) : field_or_node = Node {name; children = []}
  
let leaf_opt (name : string) : field_or_node option = Some (leaf name)

let field_leaf (field_name : string) (name : string) : field_or_node =
  Field (field_name, {name; children = []})

let field_leaf_opt (field_name : string) (name : string) : field_or_node option =
  Some (field_leaf field_name name)

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

let translate_extends (tree : Tlapm_lib__Util.hints) : field_or_node list =
  match tree with
  | [] -> []
  | _ -> [(Node {
    name = "extends";
    children = (List.map (fun _ -> leaf "identifier_ref") tree)
  })]

let translate_module (tree : Tlapm_lib__M_t.mule) : ts_node =
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
          [leaf "double_line"];
        ]
      }
    ]
  }
