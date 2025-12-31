let source_to_sany_xml_str (module_path : string) (stdlib_path : string) : (string, (string * int)) result =
  let open Unix in
  let open Paths in
  let (stdout, stdin, stderr) =
    Unix.open_process_args_full
      "java"
      [|"java"; "-cp"; backend_classpath_string "tla2tools.jar"; "tla2sany.xml.XMLExporter"; "-I"; stdlib_path; "-t"; module_path|]
      (Unix.environment ())
  in let (output, err_output) = (In_channel.input_all stdout, In_channel.input_all stderr) in
  match Unix.close_process_full (stdout, stdin, stderr) with
  | WEXITED 0 -> Ok output
  | WEXITED exit_code -> Error (output ^ "\n" ^ err_output, exit_code)
  | _ -> failwith "Process terminated abnormally"

open Xmlm;;

type tree =
  | Node of Xmlm.tag * tree list
  | Value of string
[@@deriving show]

let str_to_xml (xml_str: string) : tree =
  let xml = Xmlm.make_input (`String (0, xml_str)) in
  let el tag childs = Node (tag, childs) in
  let data d = Value d in
  Xmlm.input_doc_tree ~el ~data xml |> snd

let conversion_failure fn_name xml =
  let err_msg = Printf.sprintf "%s conversion failure on %s" fn_name (show_tree xml) in
  Invalid_argument err_msg |> raise

let is_tag (tag_name : string) (node : tree) =
  match node with
  | Node (((_, name), _), _) -> String.equal name tag_name
  | _ -> false

let children_of (xml : tree) =
  match xml with
  | Node (_, children) -> children
  | Value _ -> Invalid_argument (Printf.sprintf "Cannot get children of node %s" (show_tree xml)) |> raise

let child_of (xml : tree) =
  match xml with
  | Node (_, [child]) -> child
  | Node (_, _) -> Invalid_argument (Printf.sprintf "Require single child of node %s" (show_tree xml)) |> raise
  | Value _ -> Invalid_argument (Printf.sprintf "Cannot get children of node %s" (show_tree xml)) |> raise

let show_tree_list (xs : tree list) =
  Printf.sprintf "[%s]" (xs |> List.map show_tree |> String.concat "; ")

let find_tag (tag_name : string) (children : tree list) =
  match List.find_opt (is_tag tag_name) children with
  | Some v -> v
  | None -> Invalid_argument (Printf.sprintf "Unable to find tag %s in children %s" tag_name (show_tree_list children)) |> raise

let xml_to_tagged_string (tag_name : string) (children : tree list) =
  match find_tag tag_name children with
  | (Node (_, [Value d])) -> d
  | xml -> conversion_failure __FUNCTION__ xml

let xml_child_to_int xml =
  match xml with
  | (Node (_, [Value d])) -> int_of_string d
  | _ -> conversion_failure __FUNCTION__ xml
  
let xml_to_tagged_int (tag_name : string) (children : tree list) : int =
  find_tag tag_name children |> xml_child_to_int

type range = {
  start   : int;
  finish  : int;
}
[@@deriving show]

let xml_to_range xml =
  match xml with
  | Node (((_, _), _), children) -> {
      start = children |> xml_to_tagged_int "begin";
      finish = children |> xml_to_tagged_int "end";
    }
  | _ -> conversion_failure __FUNCTION__ xml

type location = {
  column    : range;
  line      : range;
  filename  : string;
}
[@@deriving show]

let xml_to_location xml =
  match xml with
  | Node (((_, "location"), _), children) -> {
      column = children |> find_tag "column" |> xml_to_range;
      line = children |> find_tag "line" |> xml_to_range;
      filename = children |> xml_to_tagged_string "filename";
    }
  | _ -> conversion_failure __FUNCTION__ xml

type node = {
  location  : location option;
  level     : int option;
}
[@@deriving show]

let xml_to_inline_node (children : tree list) = {
  location  = children |> List.find_opt (is_tag "location") |> Option.map xml_to_location;
  level     = children |> List.find_opt (is_tag "level") |> Option.map xml_child_to_int;
}

type numeral_node = {
  node  : node;
  value : int;
}
[@@deriving show]

let xml_to_numeral_node (xml : tree) =
  match xml with
  | Node (((_, "NumeralNode"), _), children) -> {
      node  = children |> xml_to_inline_node;
      value = children |> xml_to_tagged_int "IntValue"
    }
  | _ -> conversion_failure __FUNCTION__ xml

type formal_param_node_ref = {
  uid : int
}
[@@deriving show]

let xml_to_formal_param_node_ref xml =
  match xml with
  | Node (((_, "FormalParamNodeRef"), _), children) -> {
    uid = children |> xml_to_tagged_int "UID";
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
  | Node (((_, "FormalParamNode"), _), children) -> {
    node        = xml_to_inline_node children;
    uniquename  = xml_to_tagged_string "uniquename" children;
    arity       = xml_to_tagged_int "arity" children;
  }
  | _ -> conversion_failure __FUNCTION__ xml

type unbound_symbol = {
  formal_param_node_ref : formal_param_node_ref;
  is_tuple : bool;
}
[@@deriving show]

let xml_to_unbound_symbol xml =
  match xml with
  | Node (((_, "unbound"), _), children) -> {
    formal_param_node_ref = children |> find_tag "FormalParamNodeRef" |> xml_to_formal_param_node_ref;
    is_tuple = children |> List.exists (is_tag "tuple")
  }
  | _ -> conversion_failure __FUNCTION__ xml

type op_appl_node = {
  node      : node;
  operands  : expr_or_op_arg list;
  bound_symbols : symbols list;
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
  formal_param_node_refs : formal_param_node_ref list;
  is_tuple : bool;
  expression : expression
}

and symbols =
  | Unbound of unbound_symbol
  | Bound of bound_symbol
[@@deriving show]

let rec xml_to_symbols xml =
  match xml with
  | Node (((_, "unbound"), _), _) -> Unbound (xml_to_unbound_symbol xml)
  | Node (((_, "bound"), _), _) -> Bound (xml_to_bound_symbol xml)
  | _ -> conversion_failure __FUNCTION__ xml

and xml_to_bound_symbol xml =
  match xml with
  | Node (((_, "bound"), _), children) -> {
    formal_param_node_refs = children |> List.filter (is_tag "FormalParamNodeRef") |> List.map xml_to_formal_param_node_ref;
    is_tuple = children |> List.exists (is_tag "tuple");
    expression = children |> xml_to_inline_expression |> Option.get;
  }
  | _ -> conversion_failure __FUNCTION__ xml

and xml_to_expr_or_op_arg xml =
  try Expression (xml_to_expression xml)
with Invalid_argument _ -> conversion_failure __FUNCTION__ xml

and xml_to_op_appl_node xml =
  match xml with
  | Node (((_, "OpApplNode"), _), children) -> {
    node    = children |> xml_to_inline_node;
    operands = children |> find_tag "operands" |> children_of |> List.map xml_to_expr_or_op_arg;
    bound_symbols = children |> List.find_opt (is_tag "boundSymbols") |> Option.map children_of |> Option.value ~default:[] |> List.map xml_to_symbols;
  }
  | _ -> conversion_failure __FUNCTION__ xml

and xml_to_expression xml =
  match xml with
  | Node (((_, "NumeralNode"), _), _) -> NumeralNode (xml_to_numeral_node xml)
  | Node (((_, "OpApplNode"), _), _) -> OpApplNode (xml_to_op_appl_node xml)
  | _ -> conversion_failure __FUNCTION__ xml

and xml_to_inline_expression children =
  children
  |> List.find_opt (fun xml -> is_tag "NumeralNode" xml || is_tag "OpApplNode" xml)
  |> Option.map xml_to_expression

type module_node_ref = {
  uid : int
}
[@@deriving show]

let xml_to_module_node_ref xml =
  match xml with
  | Node (((_, "ModuleNodeRef"), _), children) -> {
      uid = children |> xml_to_tagged_int "UID";
    }
  | _ -> conversion_failure __FUNCTION__ xml

type module_node = {
  location : location;
  uniquename : string;
  units : [`Ref of int | `OtherTODO of string] list;
}
[@@deriving show]

let xml_to_module_node xml =
  let ref_child child =
    match child with
    | Node (((_, "OpDeclNodeRef"), _), children) -> Some (`Ref (xml_to_tagged_int "UID" children))
    | Node (((_, "ModuleInstanceKindRef"), _), children) -> Some (`Ref (xml_to_tagged_int "UID" children))
    | Node (((_, "UserDefinedOpKindRef"), _), children) -> Some (`Ref (xml_to_tagged_int "UID" children))
    | Node (((_, "BuiltInKindRef"), _), children) -> Some (`Ref (xml_to_tagged_int "UID" children))
    | Node (((_, "TheoremDefRef"), _), children) -> Some (`Ref (xml_to_tagged_int "UID" children))
    | Node (((_, "AssumeDefRef"), _), children) -> Some (`Ref (xml_to_tagged_int "UID" children))
    | Node (((_, "AssumeNodeRef"), _), children) -> Some (`Ref (xml_to_tagged_int "UID" children))
    | Node (((_, "TheoremNodeRef"), _), children) -> Some (`Ref (xml_to_tagged_int "UID" children))
    | Node (((_, "InstanceNode"), _), children) -> Some (`OtherTODO "InstanceNode")
    | Node (((_, "UseOrHideNode"), _), children) -> Some (`OtherTODO "UseOrHideNode")
    | _ -> None
  in match xml with
  | Node (((_, "ModuleNode"), _), children) -> {
      uniquename = children |> xml_to_tagged_string "uniquename";
      location = children |> find_tag "location" |> xml_to_location;
      units = List.filter_map ref_child children
    }
  | _ -> conversion_failure __FUNCTION__ xml

type op_decl_node = {
  uniquename : string
}
[@@deriving show]

let xml_to_op_decl_node (xml : tree) : op_decl_node =
  match xml with
  | Node (((_, "OpDeclNode"), _), children) -> ({
      uniquename = children |> xml_to_tagged_string "uniquename";
    } : op_decl_node)
  | _ -> conversion_failure __FUNCTION__ xml

type leibniz_param = {
  ref         : formal_param_node_ref;
  is_leibniz  : bool;
}
[@@deriving show]

let xml_to_leibniz_param xml =
  match xml with
  | Node (((_, "leibnizparam"), _), children) -> {
      ref         = children |> find_tag "FormalParamNodeRef" |> xml_to_formal_param_node_ref;
      is_leibniz  = children |> List.exists (is_tag "leibniz");
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
  | Node (((_, "UserDefinedOpKind"), _), children) -> {
      node        = children |> xml_to_inline_node;
      uniquename  = children |> xml_to_tagged_string  "uniquename";
      arity       = children |> xml_to_tagged_int     "arity";
      body        = children |> find_tag "body" |> child_of |> xml_to_expression;
      params      = children |> List.find_opt (is_tag "params") |> Option.map children_of |> Option.value ~default:[] |> List.map xml_to_leibniz_param;
      recursive   = children |> List.exists (is_tag "recursive");
    }
  | _ -> conversion_failure __FUNCTION__ xml

type user_defined_op_kind_ref = {
  uid : int
}
[@@deriving show]

let xml_to_user_defined_op_kind_ref xml =
  match xml with
  | Node (((_, "UserDefinedOpKindRef"), _), children) -> {
    uid = children |> xml_to_tagged_int "UID";
  }
  | _ -> conversion_failure __FUNCTION__ xml

type built_in_kind = {
  uniquename : string
}
[@@deriving show]

let xml_to_built_in_kind xml : built_in_kind =
  match xml with
  | Node (((_, "BuiltInKind"), _), children) -> {
      uniquename = children |> xml_to_tagged_string "uniquename";
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
  | Node (((_, "TheoremDefNode"), _), children) -> {
      node = children |> xml_to_inline_node;
      uniquename = children |> xml_to_tagged_string "uniquename";
      body = children |> xml_to_inline_expr_or_assume_prove |> Option.get ;
    }
  | _ -> conversion_failure __FUNCTION__ xml

type theorem_def_ref = {
  uid : int
}
[@@deriving show]

let xml_to_theorem_def_ref xml =
  match xml with
  | Node (((_, "TheoremDefRef"), _), children) -> {
      uid = xml_to_tagged_int "UID" children
    }
  | _ -> conversion_failure __FUNCTION__ xml

type theorem_node_ref = {
  uid : int
}
[@@deriving show]

let xml_to_theorem_node_ref xml =
  match xml with
  | Node (((_, "TheoremNodeRef"), _), children) -> {
      uid = xml_to_tagged_int "UID" children
    }
  | _ -> conversion_failure __FUNCTION__ xml


type omitted_proof_node = {
  node : node
}
[@@deriving show]

let xml_to_omitted_proof_node xml =
  match xml with
  | Node (((_, "omitted"), _), children) -> {
    node = children |> xml_to_inline_node;
  }
  | _ -> conversion_failure __FUNCTION__ xml

type obvious_proof_node = {
  node : node
}
[@@deriving show]

let xml_to_obvious_proof_node xml =
  match xml with
  | Node (((_, "obvious"), _), children) -> {
    node = children |> xml_to_inline_node;
  }
  | _ -> conversion_failure __FUNCTION__ xml

type definition_reference =
  | UserDefinedOpKindRef of user_defined_op_kind_ref
  | TheoremDefRef of theorem_def_ref
[@@deriving show]

let xml_to_definition_reference xml =
  match xml with
  | Node (((_, "UserDefinedOpKindRef"), _), _) -> UserDefinedOpKindRef (xml_to_user_defined_op_kind_ref xml)
  | Node (((_, "TheoremDefRef"), _), _) -> TheoremDefRef (xml_to_theorem_def_ref xml)
  | _ -> conversion_failure __FUNCTION__ xml

type by_proof_node = {
  node  : node;
  facts : expression list;
  defs  : definition_reference list;
}
[@@deriving show]

let xml_to_by_proof_node xml =
  match xml with
  | Node (((_, "by"), _), children) -> {
      node  = children |> xml_to_inline_node;
      facts = children |> List.find_opt (is_tag "facts") |> Option.map children_of |> Option.value ~default:[] |> List.map xml_to_expression;
      defs = children |> List.find_opt (is_tag "defs") |> Option.map children_of |> Option.value ~default:[] |> List.map xml_to_definition_reference;
    }
  | _ -> conversion_failure __FUNCTION__ xml

type proof_step_group =
  | TheoremNodeRef of theorem_node_ref
[@@deriving show]

let xml_to_inline_list_proof_step_group children =
  children
  |> List.filter (is_tag "TheoremNodeRef")
  |> List.map xml_to_theorem_node_ref
  |> List.map (fun node -> TheoremNodeRef node)

type steps_proof_node = {
  node  : node;
  steps : proof_step_group list;
}
[@@deriving show]

let xml_to_steps_proof_node xml =
  match xml with
  | Node (((_, "steps"), _), children) -> {
      node  = children |> xml_to_inline_node;
      steps = children |> xml_to_inline_list_proof_step_group;
    }
  | _ -> conversion_failure __FUNCTION__ xml

type proof_node_group =
  | Omitted of omitted_proof_node
  | Obvious of obvious_proof_node
  | By of by_proof_node
  | Steps of steps_proof_node
[@@deriving show]

let xml_to_inline_proof_node_group children =
  let rec search_children ls =
    match ls with
    | x::xs -> (
        match x with
        | Node (((_, "omitted"), _), _) -> Omitted (xml_to_omitted_proof_node x)
        | Node (((_, "obvious"), _), _) -> Obvious (xml_to_obvious_proof_node x)
        | Node (((_, "by"), _), _) -> By (xml_to_by_proof_node x)
        | Node (((_, "steps"), _), _) -> Steps (xml_to_steps_proof_node x)
        | _ -> search_children xs
      )
    | _ -> conversion_failure __FUNCTION__ (List.hd children)
  in search_children children

type theorem_node = {
  node        : node;
  definition  : theorem_def_ref option;
  body        : expr_or_assume_prove;
  proof       : proof_node_group;
}
[@@deriving show]

let xml_to_theorem_node xml =
  match xml with
  | Node (((_, "TheoremNode"), _), children) -> {
      node        = children |> xml_to_inline_node;
      definition  = children |> List.find_opt (is_tag "definition") |> Option.map child_of |> Option.map xml_to_theorem_def_ref;
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

let xml_to_entry_kind (children : tree list) =
  let rec find_variant (candidates : tree list) =
    match candidates with
    | x :: xs -> (
      match x with
      | Node (((_, "ModuleNode"), _), _)        -> ModuleNode (xml_to_module_node x)
      | Node (((_, "OpDeclNode"), _), _)        -> OpDeclNode (xml_to_op_decl_node x)
      | Node (((_, "UserDefinedOpKind"), _), _) -> UserDefinedOpKind (xml_to_user_defined_op_kind x)
      | Node (((_, "BuiltInKind"), _), _)       -> BuiltInKind (xml_to_built_in_kind x)
      | Node (((_, "FormalParamNode"), _), _)   -> FormalParamNode (xml_to_formal_param_node x)
      | Node (((_, "TheoremDefNode"), _), _)    -> TheoremDefNode (xml_to_theorem_def_node x)
      | Node (((_, "TheoremNode"), _), _)       -> TheoremNode (xml_to_theorem_node x)
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
  | Node (((_, "entry"), _), children) -> {
      uid = children |> xml_to_tagged_int "UID";
      kind = xml_to_entry_kind children;
    }
  | _ -> conversion_failure __FUNCTION__ xml

type context = {
  entry : entry list
}
[@@deriving show]

let xml_to_context xml =
  match xml with
  | Node (((_, "context"), _), children) -> {
      entry = children |> List.find_all (is_tag "entry") |> List.map xml_to_entry;
    }
  | _ -> conversion_failure __FUNCTION__ xml

type modules = {
  root_module: string;
  context: context;
  module_node_ref : module_node_ref list;
  module_node : module_node list;
}
[@@deriving show]

let xml_to_modules xml =
  match xml with
  | Node (((_, "modules"), _), children) -> {
      root_module = xml_to_tagged_string "RootModule" children;
      context = children |> find_tag "context" |> xml_to_context;
      module_node_ref = children |> List.find_all (is_tag "ModuleNodeRef") |> List.map xml_to_module_node_ref;
      module_node = children |> List.find_all (is_tag "ModuleNode") |> List.map xml_to_module_node;
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

let ( >>= ) = Result.bind

let get_module_ast_xml (module_path : string) (stdlib_path : string) : (modules, (string option * string)) result =
  match source_to_sany_xml_str module_path stdlib_path with
  | Error (output, exit_code) -> Error (None, Printf.sprintf "%d\n%s" exit_code output)
  | Ok xml_str ->
    match xml_str |> str_to_xml |> xml_to_ast with
    | Error (msg, trace) -> Error (None, Printf.sprintf "%s\n%s" msg trace)
    | Ok ast -> ast |> Result.ok
