(** This module provides functions to interact with SANY to parse TLA+ source
    files into an XML representation, and then convert that XML representation
    into something with a semblance of a type system.
*)

(** Calls SANY in another process to parse the given TLA+ file, then collects
    the XML parse tree output.
*)
let source_to_sany_xml_str (module_path : string) (stdlib_path : string) : (string, (string * int)) result =
  let open Unix in
  let open Paths in
  let cmd = Printf.sprintf "java -cp %s tla2sany.xml.XMLExporter -I %s -t %s" 
    (backend_classpath_string "tla2tools.jar") 
    (Filename.quote stdlib_path) 
    (Filename.quote module_path) in
  let (pid, out_fd) = System.launch_process cmd in
  let in_chan = Unix.in_channel_of_descr out_fd in
  let output = In_channel.input_all in_chan in
  In_channel.close in_chan;
  match Unix.waitpid [] pid with
  | (_, WEXITED 0) -> Ok output
  | (_, WEXITED exit_code) -> Error (output, exit_code)
  | _ -> failwith "Process terminated abnormally"

open Xmlm;;

(** This simple XML representation only consists of nodes and values, where
    node is a tag with a list of children. For example, the XML snippet
    <SomeName>"value"</SomeName> would be Node ("SomeName", [Value "value"]).
    XML can also have attributes on tags, like <SomeName attr="value">, but
    these are not used in SANY's XML format.
*)
type tree =
  | Node of string * tree list
  | Value of string
[@@deriving show]

(** Uses the Xmlm library to parse an XML string into the simple XML tree
    representation defined above.
*)
let str_to_xml (xml_str: string) : tree =
  let xml = Xmlm.make_input (`String (0, xml_str)) in
  let el (((_, name), _) : tag) (children : tree list) = Node (name, children) in
  let data (d : string) = Value d in
  Xmlm.input_doc_tree ~el ~data xml |> snd

(** Error method which raises an exception when parsing the SANY XML output
    fails. If this is ever triggered it indicates a bug either in this code
    (most likely) or in the SANY XML output. It is also possible this could
    be triggered if SANY's XML output format changes in a future version.
*)
let conversion_failure (fn_name : string) (xml : tree) : 'a =
  let err_msg = Printf.sprintf "%s conversion failure on %s" fn_name (show_tree xml) in
  Invalid_argument err_msg |> raise

(** Utility function most often used with List.find or List.exists to search
    for a tag in the children of an XML node.
*)
let is_tag (tag_name : string) (node : tree) : bool =
  match node with
  | Node (name, _) -> String.equal name tag_name
  | _ -> false

(** Utility function that simply returns the children of an XML node. Raises
    an exception if called on a leaf node.
*)
let children_of (xml : tree) : tree list =
  match xml with
  | Node (_, children) -> children
  | Value _ -> Invalid_argument (Printf.sprintf "Cannot get children of node %s" (show_tree xml)) |> raise

(** Utility function that returns the single child of an XML node. Raises an
    exception if there is not exactly one child.
*)
let child_of (xml : tree) : tree =
  match xml with
  | Node (_, [child]) -> child
  | Node (_, _) -> Invalid_argument (Printf.sprintf "Require single child of node %s" (show_tree xml)) |> raise
  | Value _ -> Invalid_argument (Printf.sprintf "Cannot get children of node %s" (show_tree xml)) |> raise

(** Utility function to print a list of XML trees for debugging or error
    message purposes.
*)
let show_tree_list (xs : tree list) : string =
  Printf.sprintf "[%s]" (xs |> List.map show_tree |> String.concat "; ")

(** Searches for a tag in the children of an XML node, and raises a detailed
    exception if it is not found.
*)
let find_tag (tag_name : string) (children : tree list) : tree =
  match List.find_opt (is_tag tag_name) children with
  | Some v -> v
  | None -> Invalid_argument (Printf.sprintf "Unable to find tag %s in children %s" tag_name (show_tree_list children)) |> raise

(** Utility function to extract the string value from a tagged XML node.
    Raises a detailed exception if the tag is not found or if the tagged node
    does not contain a single string value.
*)
let xml_to_tagged_string (tag_name : string) (children : tree list) : string =
  match find_tag tag_name children with
  | (Node (_, [Value d])) -> d
  | xml -> conversion_failure __FUNCTION__ xml

(** Utility function to extract the int value from a tagged XML node.
    Raises a detailed exception if the tag is not found or if the tagged node
    does not contain a single int value.
*)
let xml_child_to_int (xml : tree) : int =
  match xml with
  | (Node (_, [Value d])) -> int_of_string d
  | _ -> conversion_failure __FUNCTION__ xml
  
let xml_to_tagged_int (tag_name : string) (children : tree list) : int =
  find_tag tag_name children |> xml_child_to_int

(** Use this in conjunction with List.filter_map on children of a node to get
    all references of various types.
*)
let get_ref_opt (xml : tree) : int option =
  match xml with
  | Node ("AssumeDefRef", [Node ("UID", [Value uid])]) -> Some (int_of_string uid)
  | Node ("BuiltInKindRef", [Node ("UID", [Value uid])]) -> Some (int_of_string uid)
  | Node ("FormalParamNodeRef", [Node ("UID", [Value uid])]) -> Some (int_of_string uid)
  | Node ("ModuleInstanceKindRef", [Node ("UID", [Value uid])]) -> Some (int_of_string uid)
  | Node ("ModuleNodeRef", [Node ("UID", [Value uid])]) -> Some (int_of_string uid)
  | Node ("OpDeclNodeRef", [Node ("UID", [Value uid])]) -> Some (int_of_string uid)
  | Node ("TheoremDefRef", [Node ("UID", [Value uid])]) -> Some (int_of_string uid)
  | Node ("TheoremNodeRef", [Node ("UID", [Value uid])]) -> Some (int_of_string uid)
  | Node ("UserDefinedOpKindRef", [Node ("UID", [Value uid])]) -> Some (int_of_string uid)
  | _ -> None

(** Use this either on a single node that must have a UID child, or in
    conjunction with List.map on children of a node that all must have UID
    children.
*)
let get_ref (xml : tree) : int =
  match get_ref_opt xml with
  | Some uid -> uid
  | _ -> conversion_failure __FUNCTION__ xml

type location = {
  column    : int * int;
  line      : int * int;
  filename  : string;
}
[@@deriving show]

let xml_to_location (xml : tree) : location =
  match xml with
  | Node ("location", [
    Node ("column", [Node ("begin", [Value column_begin]); Node ("end", [Value column_end])]);
    Node ("line", [Node ("begin", [Value line_begin]); Node ("end", [Value line_end])]);
    Node ("filename", [Value filename])
  ]) -> {
      column = (int_of_string column_begin, int_of_string column_end);
      line = (int_of_string line_begin, int_of_string line_end);
      filename;
    }
  | _ -> conversion_failure __FUNCTION__ xml

type level =
  | Constant
  | Variable
  | Action
  | Temporal
[@@deriving show]

let int_to_level (n : int) : level =
  match n with
  | 0 -> Constant
  | 1 -> Variable
  | 2 -> Action
  | 3 -> Temporal
  | _ -> Invalid_argument (Printf.sprintf "Invalid level value: %d" n) |> raise

type node = {
  location  : location option;
  level     : level option;
}
[@@deriving show]

(** Many XML nodes have children that start with some optional "location" and
    "level" tags, followed by other tags specific to that node. This function
    extracts the location and level information from such a list of children,
    then returns the remaining children for further processing.
*)
let extract_inline_node (children : tree list) : (node * tree list) =
  match children with
  | Node ("location", _) as loc :: Node ("level", [Value lvl]) :: rest -> {location = Some (xml_to_location loc); level = Some (lvl |> int_of_string |> int_to_level)}, rest
  | Node ("location", _) as loc :: rest -> {location = Some (xml_to_location loc); level = None}, rest
  | Node ("level", [Value lvl]) :: rest -> {location = None; level = Some (lvl |> int_of_string |> int_to_level)}, rest
  | rest -> {location = None; level = None}, rest

type numeral_node = {
  node  : node;
  value : int;
}
[@@deriving show]

let xml_to_numeral_node (xml : tree) =
  match xml with
  | Node ("NumeralNode", children) ->
    let (node, children) = extract_inline_node children in {
      node;
      value = children |> xml_to_tagged_int "IntValue"
    }
  | _ -> conversion_failure __FUNCTION__ xml

type formal_param_node = {
  node        : node;
  uniquename  : string;
  arity       : int;
}
[@@deriving show]

let xml_to_formal_param_node xml =
  match xml with
  | Node ("FormalParamNode", children) ->
    let (node, children) = extract_inline_node children in {
    node;
    uniquename  = xml_to_tagged_string "uniquename" children;
    arity       = xml_to_tagged_int "arity" children;
  }
  | _ -> conversion_failure __FUNCTION__ xml

type unbound_symbol = {
  symbol_ref : int;
  is_tuple : bool;
}
[@@deriving show]

let xml_to_unbound_symbol xml =
  match xml with
  | Node ("unbound", Node ("FormalParamNodeRef", [Node ("UID", [Value uid])]) :: tuple_tag_opt) -> {
    symbol_ref = int_of_string uid;
    is_tuple = match tuple_tag_opt with | [Node ("tuple", [])] -> true | _ -> false;
  }
  | _ -> conversion_failure __FUNCTION__ xml

type op_appl_node = {
  node      : node;
  operator  : int;
  operands  : expr_or_op_arg list;
  bound_symbols : symbol list;
}
[@@deriving show]

and expression =
(*| AtNode of at_node*)
(*| DecimalNode of decimal_node*)
(*| LabelNode of label_node*)
(*| LetInNode of let_in_node*)
  | NumeralNode of numeral_node
  | OpApplNode of op_appl_node
(*| StringNode of string_node*)
(*| SubstInNode of subst_in_node*)
(*| TheoremDefRef of theorem_def_ref*)
(*| AssumeDefRef of assume_def_ref*)

and expr_or_op_arg =
  | Expression of expression
(*| OpArg of operator_arg*)

and bound_symbol = {
  symbol_refs : int list;
  is_tuple : bool;
  expression : expression
}

and symbol =
  | Unbound of unbound_symbol
  | Bound of bound_symbol
[@@deriving show]

let rec xml_to_symbols xml =
  match xml with
  | Node ("unbound", _) -> Unbound (xml_to_unbound_symbol xml)
  | Node ("bound", _) -> Bound (xml_to_bound_symbol xml)
  | _ -> conversion_failure __FUNCTION__ xml

and xml_to_bound_symbol xml =
  match xml with
  | Node ("bound", children) -> {
    symbol_refs = children |> List.filter_map get_ref_opt;
    is_tuple = children |> List.exists (is_tag "tuple");
    expression = children |> xml_to_inline_expression |> Option.get;
  }
  | _ -> conversion_failure __FUNCTION__ xml

and xml_to_expr_or_op_arg xml =
  try Expression (xml_to_expression xml)
with Invalid_argument _ -> conversion_failure __FUNCTION__ xml

and xml_to_op_appl_node xml =
  match xml with
  | Node ("OpApplNode", children) -> 
    let (node, children) = extract_inline_node children in {
    node;
    operator = children |> find_tag "operator" |> child_of |> get_ref;
    operands = children |> find_tag "operands" |> children_of |> List.map xml_to_expr_or_op_arg;
    bound_symbols = children |> List.find_opt (is_tag "boundSymbols") |> Option.map children_of |> Option.value ~default:[] |> List.map xml_to_symbols;
  }
  | _ -> conversion_failure __FUNCTION__ xml

and xml_to_expression xml =
  match xml with
  | Node ("NumeralNode", _) -> NumeralNode (xml_to_numeral_node xml)
  | Node ("OpApplNode", _) -> OpApplNode (xml_to_op_appl_node xml)
  | _ -> conversion_failure __FUNCTION__ xml

and xml_to_inline_expression children =
  children
  |> List.find_opt (fun xml -> is_tag "NumeralNode" xml || is_tag "OpApplNode" xml)
  |> Option.map xml_to_expression

type module_node = {
  location : location;
  uniquename : string;
  units : [`Ref of int | `OtherTODO of string] list;
}
[@@deriving show]

let xml_to_module_node xml =
  let ref_child child =
    match child with
    | Node ("OpDeclNodeRef", [Node ("UID", [Value uid])]) -> Some (`Ref (int_of_string uid))
    | Node ("ModuleInstanceKindRef", [Node ("UID", [Value uid])]) -> Some (`Ref (int_of_string uid))
    | Node ("UserDefinedOpKindRef", [Node ("UID", [Value uid])]) -> Some (`Ref (int_of_string uid))
    | Node ("BuiltInKindRef", [Node ("UID", [Value uid])]) -> Some (`Ref (int_of_string uid))
    | Node ("TheoremDefRef", [Node ("UID", [Value uid])]) -> Some (`Ref (int_of_string uid))
    | Node ("AssumeDefRef", [Node ("UID", [Value uid])]) -> Some (`Ref (int_of_string uid))
    | Node ("AssumeNodeRef", [Node ("UID", [Value uid])]) -> Some (`Ref (int_of_string uid))
    | Node ("TheoremNodeRef", [Node ("UID", [Value uid])]) -> Some (`Ref (int_of_string uid))
    | Node ("InstanceNode", children) -> Some (`OtherTODO "InstanceNode")
    | Node ("UseOrHideNode", children) -> Some (`OtherTODO "UseOrHideNode")
    | _ -> None
  in match xml with
  | Node ("ModuleNode", children) -> {
      uniquename = children |> xml_to_tagged_string "uniquename";
      location = children |> find_tag "location" |> xml_to_location;
      units = List.filter_map ref_child children
    }
  | _ -> conversion_failure __FUNCTION__ xml
  
type declaration_kind =
  | Variable
[@@deriving show]

let int_to_declaration_kind (n : int) : declaration_kind =
  match n with
  | 3 -> Variable
  | _ -> Invalid_argument (Printf.sprintf "Invalid declaration kind value: %d" n) |> raise

type op_decl_node = {
  node       : node;
  uniquename : string;
  arity      : int;
  kind       : declaration_kind;
}
[@@deriving show]

let xml_to_op_decl_node (xml : tree) : op_decl_node =
  match xml with
  | Node ("OpDeclNode", children) ->
    let (node, children) = extract_inline_node children in {
      node;
      uniquename = children |> xml_to_tagged_string "uniquename";
      arity = children |> xml_to_tagged_int "arity";
      kind = children |> xml_to_tagged_int "kind" |> int_to_declaration_kind;
    }
  | _ -> conversion_failure __FUNCTION__ xml

type leibniz_param = {
  ref         : int;
  is_leibniz  : bool;
}
[@@deriving show]

let xml_to_leibniz_param xml =
  match xml with
  | Node ("leibnizparam", Node ("FormalParamNodeRef", [Node ("UID", [Value uid])]) :: is_leibniz_opt) -> {
      ref         = int_of_string uid;
      is_leibniz  = match is_leibniz_opt with | [Node ("leibniz", [])] -> true | _ -> false;
    }
  | _ -> conversion_failure __FUNCTION__ xml

type user_defined_op_kind = {
  node        : node;
  uniquename  : string;
  arity       : int;
  body        : expression;
  params      : leibniz_param list;
  recursive   : bool;
}
[@@deriving show]

let xml_to_user_defined_op_kind xml : user_defined_op_kind =
  match xml with
  | Node ("UserDefinedOpKind", children) ->
    let (node, children) = extract_inline_node children in {
      node;
      uniquename  = children |> xml_to_tagged_string  "uniquename";
      arity       = children |> xml_to_tagged_int     "arity";
      body        = children |> find_tag "body" |> child_of |> xml_to_expression;
      params      = children |> List.find_opt (is_tag "params") |> Option.map children_of |> Option.value ~default:[] |> List.map xml_to_leibniz_param;
      recursive   = children |> List.exists (is_tag "recursive");
    }
  | _ -> conversion_failure __FUNCTION__ xml

type built_in_kind = {
  node       : node;
  uniquename : string;
  arity      : int;
  params     : leibniz_param list;
}
[@@deriving show]

let xml_to_built_in_kind xml : built_in_kind =
  match xml with
  | Node ("BuiltInKind", children) ->
    let (node, children) = extract_inline_node children in {
      node;
      uniquename = children |> xml_to_tagged_string "uniquename";
      arity      = children |> xml_to_tagged_int "arity";
      params     = children |> List.find_opt (is_tag "params") |> Option.map children_of |> Option.value ~default:[] |> List.map xml_to_leibniz_param;
    }
  | _ -> conversion_failure __FUNCTION__ xml

type expr_or_assume_prove =
  | Expression of expression
(*| AssumeProveLike of assume_prove_like*)
[@@deriving show]

let xml_to_inline_expr_or_assume_prove children =
  match xml_to_inline_expression children with
  | Option.Some expr -> Option.Some (Expression expr)
  | Option.None -> (*TODO: try-match assume-prove*) Option.None

type theorem_def_node = {
  node        : node;
  uniquename  : string;
  body        : expr_or_assume_prove;
}
[@@deriving show]

let xml_to_theorem_def_node xml =
  match xml with
  | Node ("TheoremDefNode", children) -> 
    let (node, children) = extract_inline_node children in {
      node;
      uniquename = children |> xml_to_tagged_string "uniquename";
      body = children |> xml_to_inline_expr_or_assume_prove |> Option.get ;
    }
  | _ -> conversion_failure __FUNCTION__ xml

type by_proof_node = {
  node  : node;
  facts : expression list;
  defs  : int list;
}
[@@deriving show]

let xml_to_by_proof_node xml =
  match xml with
  | Node ("by", children) ->
    let (node, children) = extract_inline_node children in {
      node;
      facts = children |> find_tag "facts" |> children_of |> List.map xml_to_expression;
      defs = children |> find_tag "defs" |> children_of |> List.filter_map get_ref_opt
    }
  | _ -> conversion_failure __FUNCTION__ xml

type proof_step_group =
  | TheoremNodeRef of int
  (* TODO
  | DefStepNode
  | UseOrHideNode
  | InstanceNode
  | TheoremNode
  *)
[@@deriving show]

let xml_to_proof_step_group xml =
  match xml with
  | Node ("TheoremNodeRef", [Node ("UID", [Value uid])]) -> TheoremNodeRef (int_of_string uid)
  | _ -> conversion_failure __FUNCTION__ xml

type steps_proof_node = {
  node  : node;
  steps : proof_step_group list;
}
[@@deriving show]

let xml_to_steps_proof_node xml =
  match xml with
  | Node ("steps", children) ->
    let (node, steps) = extract_inline_node children in {
      node;
      steps = List.map xml_to_proof_step_group steps
    }
  | _ -> conversion_failure __FUNCTION__ xml

type proof_node_group =
  | Omitted of node
  | Obvious of node
  | By of by_proof_node
  | Steps of steps_proof_node
[@@deriving show]

let xml_to_inline_proof_node_group children =
  let rec search_children ls =
    match ls with
    | x::xs -> (
        match x with
        | Node ("omitted", children) -> let (node, _) = extract_inline_node children in Omitted node
        | Node ("obvious", children) -> let (node, _) = extract_inline_node children in Obvious node
        | Node ("by", _) -> By (xml_to_by_proof_node x)
        | Node ("steps", _) -> Steps (xml_to_steps_proof_node x)
        | _ -> search_children xs
      )
    | _ -> conversion_failure __FUNCTION__ (List.hd children)
  in search_children children

type theorem_node = {
  node        : node;
  definition  : int option;
  body        : expr_or_assume_prove;
  proof       : proof_node_group;
}
[@@deriving show]

let xml_to_theorem_node xml =
  match xml with
  | Node ("TheoremNode", children) -> 
    let (node, children) = extract_inline_node children in {
      node;
      definition  = children |> List.find_opt (is_tag "definition") |> Option.map child_of |> Option.map get_ref;
      body        = children |> find_tag "body" |> children_of |> xml_to_inline_expr_or_assume_prove |> Option.get;
      proof       = children |> xml_to_inline_proof_node_group;
    }
  | _ -> conversion_failure __FUNCTION__ xml

type entry_kind =
  | ModuleNode of module_node
  | OpDeclNode of op_decl_node
  | UserDefinedOpKind of user_defined_op_kind
  | BuiltInKind of built_in_kind
  | FormalParamNode of formal_param_node
  | TheoremDefNode of theorem_def_node
  | TheoremNode of theorem_node
[@@deriving show]

let xml_to_entry_kind (children : tree list) : entry_kind =
  let rec find_variant (candidates : tree list) =
    match candidates with
    | x :: xs -> (
      match x with
      | Node ("ModuleNode", _)        -> ModuleNode (xml_to_module_node x)
      | Node ("OpDeclNode", _)        -> OpDeclNode (xml_to_op_decl_node x)
      | Node ("UserDefinedOpKind", _) -> UserDefinedOpKind (xml_to_user_defined_op_kind x)
      | Node ("BuiltInKind", _)       -> BuiltInKind (xml_to_built_in_kind x)
      | Node ("FormalParamNode", _)   -> FormalParamNode (xml_to_formal_param_node x)
      | Node ("TheoremDefNode", _)    -> TheoremDefNode (xml_to_theorem_def_node x)
      | Node ("TheoremNode", _)       -> TheoremNode (xml_to_theorem_node x)
      | _ -> find_variant xs
    )
    | [] -> Invalid_argument (Printf.sprintf "Unable to find entry_kind variant in children %s" (show_tree_list children)) |> raise
  in find_variant children

type entry = {
  uid : int;
  kind : entry_kind;
}
[@@deriving show]

let xml_to_entry xml =
  match xml with
  | Node ("entry", children) -> {
      uid = children |> xml_to_tagged_int "UID";
      kind = xml_to_entry_kind children;
    }
  | _ -> conversion_failure __FUNCTION__ xml

type modules = {
  root_module: string;
  context: entry list;
  module_node_ref : int list;
}
[@@deriving show]

let xml_to_modules xml =
  let xml_to_context xml =
    match xml with
    | Node ("context", children) ->
        children |> List.find_all (is_tag "entry") |> List.map xml_to_entry;
    | _ -> conversion_failure __FUNCTION__ xml
  in match xml with
  | Node ("modules", children) -> {
      root_module = xml_to_tagged_string "RootModule" children;
      context = children |> find_tag "context" |> xml_to_context;
      module_node_ref = children |> List.filter_map get_ref_opt
    }
  | _ -> conversion_failure __FUNCTION__ xml

let xml_to_ast (xml : tree) : (modules, (string * string)) result =
  let prev_backtrace = Printexc.backtrace_status () in
  if Params.debugging "sany" then Printexc.record_backtrace true;
  try
    let modules = xml_to_modules xml in
    Printexc.record_backtrace prev_backtrace;
    Result.ok modules
  with Invalid_argument e ->
    let trace = Printexc.get_backtrace () in
    Printexc.record_backtrace prev_backtrace;
    Result.error (e, trace)

let get_module_ast_xml (module_path : string) (stdlib_path : string) : (modules, (string option * string)) result =
  match source_to_sany_xml_str module_path stdlib_path with
  | Error (output, exit_code) -> Error (None, Printf.sprintf "%d\n%s" exit_code output)
  | Ok xml_str ->
    match xml_str |> str_to_xml |> xml_to_ast with
    | Error (msg, trace) -> Error (None, Printf.sprintf "%s\n%s" msg trace)
    | Ok ast -> ast |> Result.ok
