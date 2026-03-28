(** This module provides functions to interact with SANY to parse TLA+ source
    files into an XML representation, and then convert that XML representation
    into something with a semblance of a type system. For example, different
    node types will have fields of type int or string or even a variant. This
    makes it much more tractable to convert SANY's XML output into the format
    expected by TLAPM.
*)

(** Calls SANY in another process to parse the given TLA+ file, then collects
    the XML parse tree output.
*)
let source_to_sany_xml_str (module_path : string) (stdlib_path : string) : (string, (string option * string)) result =
  let open Unix in
  let open Paths in
  (** Module jars must be appended at the end of the classpath; the reason
      for this is that some commonly-used jars like Apalache's embed SANY
      along with the XMLExporter class, so we accidentally use Apalache's
      (old) embedded version instead of the one from tla2tools.jar if we put
      Apalache earlier in the classpath.
  *)
  let cmd = Printf.sprintf "java -cp %s tla2sany.xml.XMLExporter -I %s -I %s -t %s"
    ((backend_classpath_string "tla2tools.jar") ^ (String.concat ":" !Params.module_jar_paths))
    (Filename.dirname module_path)
    (Filename.quote stdlib_path)
    (Filename.quote module_path) in
  if Params.debugging "sany" then print_endline cmd else ();
  let (pid, out_fd) = System.launch_process cmd in
  let in_chan = Unix.in_channel_of_descr out_fd in
  let output = In_channel.input_all in_chan in
  In_channel.close in_chan;
  match Unix.waitpid [] pid with
  | (_, WEXITED 0) -> Ok output
  | (_, WEXITED exit_code) -> Error (None, Printf.sprintf "%d\n%s" exit_code output)
  | _ -> failwith "Process terminated abnormally"

open Xmlm;;

(** This simple XML representation only consists of nodes and values, where
    node is a tag with a list of children. For example, the XML snippet
    <SomeName>"value"</SomeName> would be Node ("SomeName", [SValue "value"]).
    XML can also have attributes on tags, like <SomeName attr="value">, but
    these are not used in SANY's XML format.
*)
type tree =
  | Node of string * tree list
  | SValue of string
  | IValue of int
[@@deriving show]

(** Uses the Xmlm library to parse an XML string into the simple XML tree
    representation defined above. If SANY's XML output format is ever changed
    to make use of attributes or namespaces, this function and the tree type
    will both need to be updated accordingly.
*)
let str_to_xml (xml_str: string) : (tree, (string option * string)) result =
  try
    let xml = Xmlm.make_input (`String (0, xml_str)) in
    let el (((_namespace, name), _attributes) : tag) (children : tree list) = Node (name, children) in
    let data (s : string) = match int_of_string_opt s with | Some n -> IValue n | None -> SValue s in
    let _, tree = Xmlm.input_doc_tree ~el ~data xml in Ok tree
  with Xmlm.Error ((line, column), err) ->
    Error (Some (Printf.sprintf "Line: %d, Column: %d" line column), "XML parsing failed: " ^ Xmlm.error_message err)

(** Error method which raises an exception when parsing the SANY XML output
    fails. If this is ever triggered it indicates a bug either in this code
    (most likely) or in the SANY XML output. It is also possible this could
    be triggered if SANY's XML output format changes in a future version.
*)
let conversion_failure (fn_name : string) (xml : tree) : 'a =
  let err_msg = Printf.sprintf "%s conversion failure on %s" fn_name (show_tree xml) in
  Invalid_argument err_msg |> raise

(** Error method which raises an exception when parsing a list of XML
    children fails.
*)
let ls_conversion_failure (fn_name : string) (children : tree list) : 'a =
  let err_msg = Printf.sprintf "%s conversion failure on [%s]" fn_name (children |> List.map show_tree |> String.concat "; ") in
  Invalid_argument err_msg |> raise

(** Utility function most often used with List.find or List.exists to search
    for a tag in the children of an XML node.
*)
let is_tag (tag_name : string) (node : tree) : bool =
  match node with
  | Node (name, _) when name = tag_name -> true
  | _ -> false

(** Use this in conjunction with List.filter_map on children of a node to get
    all references of various types.
*)
let get_ref_opt (xml : tree) : int option =
  match xml with
  | Node ("AssumeNodeRef", [Node ("UID", [IValue uid])]) -> Some uid
  | Node ("AssumeDefRef", [Node ("UID", [IValue uid])]) -> Some uid
  | Node ("BuiltInKindRef", [Node ("UID", [IValue uid])]) -> Some uid
  | Node ("FormalParamNodeRef", [Node ("UID", [IValue uid])]) -> Some uid
  | Node ("ModuleInstanceKindRef", [Node ("UID", [IValue uid])]) -> Some uid
  | Node ("ModuleNodeRef", [Node ("UID", [IValue uid])]) -> Some uid
  | Node ("OpDeclNodeRef", [Node ("UID", [IValue uid])]) -> Some uid
  | Node ("TheoremDefRef", [Node ("UID", [IValue uid])]) -> Some uid
  | Node ("TheoremNodeRef", [Node ("UID", [IValue uid])]) -> Some uid
  | Node ("UserDefinedOpKindRef", [Node ("UID", [IValue uid])]) -> Some uid
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

let show_location (loc : location) : string =
  Printf.sprintf "Location: %s module, line %d column %d to line %d column %d"
    loc.filename
    (fst loc.line) (fst loc.column)
    (snd loc.line) (snd loc.column)

let xml_to_location (xml : tree) : location =
  match xml with
  | Node ("location", [
    Node ("column", [Node ("begin", [IValue column_begin]); Node ("end", [IValue column_end])]);
    Node ("line", [Node ("begin", [IValue line_begin]); Node ("end", [IValue line_end])]);
    Node ("filename", [SValue filename])
  ]) -> {
      column = (column_begin, column_end);
      line = (line_begin, line_end);
      filename;
    }
  | _ -> conversion_failure __FUNCTION__ xml

type node = {
  location  : location option;
  level     : int option;
}
[@@deriving show]

(** Many XML nodes have children that start with some optional "location" and
    "level" tags, followed by other tags specific to that node. This function
    extracts the location and level information from such a list of children,
    then returns the remaining children for further processing.
*)
let extract_inline_node (children : tree list) : (node * tree list) =
  match children with
  | Node ("location", _) as loc :: Node ("level", [IValue lvl]) :: rest -> {location = Some (xml_to_location loc); level = Some lvl}, rest
  | Node ("location", _) as loc :: rest -> {location = Some (xml_to_location loc); level = None}, rest
  | Node ("level", [IValue lvl]) :: rest -> {location = None; level = Some lvl}, rest
  | rest -> {location = None; level = None}, rest


(** A few XML nodes have an inline definition reference as their first child
    after the location and level tags. This function is meant to be chained
    after extract_inline_node to extract that definition reference if it
    exists.
*)
let extract_inline_definition_opt (node, children : node * tree list) : (node * int option * tree list) =
  match children with
  | Node ("definition", [Node ("AssumeDefRef", [Node ("UID", [IValue uid])])]) :: children -> (node, Some uid, children);
  | Node ("definition", [Node ("TheoremDefRef", [Node ("UID", [IValue uid])])]) :: children -> (node, Some uid, children);
  | _ -> (node, None, children)

type decimal_node = {
  node : node;
  mantissa : int;
  exponent : int;
  integralPart : int;
  fractionalPart : int
}
[@@deriving show]

let xml_to_decimal_node (children : tree list) : decimal_node =
  match extract_inline_node children with
  | node, [
      Node ("mantissa", [IValue mantissa]);
      Node ("exponent", [IValue exponent]);
      Node ("integralPart", [IValue integralPart]);
      Node ("fractionalPart", [IValue fractionalPart]);
    ] -> {
      node;
      mantissa;
      exponent;
      integralPart;
      fractionalPart;
    }
  | _ -> ls_conversion_failure __FUNCTION__ children

type 'a literal = {
  node  : node;
  value : 'a
}
[@@deriving show]

let xml_to_numeral_node (children : tree list) : int literal =
  match extract_inline_node children with
  | node, [Node ("IntValue", [IValue value])] -> {node; value}
  | _ -> ls_conversion_failure __FUNCTION__ children

let xml_to_string_node (children : tree list) : string literal =
  match extract_inline_node children with
  | node, [Node ("StringValue", [SValue value])] -> {node; value}
  (* In the case of an empty string "", node has no children *)
  | node, [Node ("StringValue", [])] -> {node; value = ""}
  (* Sometimes strings can accidentally be converted into integers! *)
  | node, [Node ("StringValue", [IValue value])] -> {node; value = Int.to_string value}
  | node, _ -> ls_conversion_failure __FUNCTION__ children

type leibniz_param = {
  ref         : int;
  is_leibniz  : bool;
}
[@@deriving show]

let xml_to_leibniz_param xml =
  match xml with
  | Node ("leibnizparam", Node ("FormalParamNodeRef", [Node ("UID", [IValue ref])]) :: is_leibniz_opt) -> {
      ref;
      is_leibniz  = match is_leibniz_opt with | [Node ("leibniz", [])] -> true | _ -> false;
    }
  | _ -> conversion_failure __FUNCTION__ xml

type formal_param_node = {
  node  : node;
  name  : string;
  arity : int;
}
[@@deriving show]

let xml_to_formal_param_node (children : tree list) : formal_param_node =
  match extract_inline_node children with
  | node, [Node ("uniquename", [SValue name]); Node ("arity", [IValue arity])] -> {node; name; arity}
  | _ -> ls_conversion_failure __FUNCTION__ children

type unbound_symbol = {
  symbol_ref : int;
  is_tuple : bool;
}
[@@deriving show]

let xml_to_unbound_symbol (children : tree list) : unbound_symbol =
  match children with
  | Node ("FormalParamNodeRef", [Node ("UID", [IValue symbol_ref])]) :: tuple_tag_opt -> {
    symbol_ref;
    is_tuple = match tuple_tag_opt with | [Node ("tuple", [])] -> true | _ -> false;
  }
  | _ -> ls_conversion_failure __FUNCTION__ children

type op_appl_node = {
  node      : node;
  operator  : int;
  operands  : expr_or_op_arg list;
  bound_symbols : symbol list;
}

and let_in_node = {
  node     : node;
  def_refs : int list;
  body     : expression;
}

and at_node = {
  node      : node;
}

and label_node = {
  node        : node;
  name        : string;
  arity       : int;
  body        : expr_or_assume_prove;
  parameters  : int list
}

and subst_in_node = {
  node : node;
  substitutions : substitution list;
  body : expression;
  instance_from_mule_ref : int;
  instance_to_mule_ref : int;
}

and substitution = {
  target_uid : int;
  substitute : expr_or_op_arg;
}

and expression =
  | AtNode of at_node
  | DecimalNode of decimal_node
  | LabelNode of label_node
  | LetInNode of let_in_node
  | NumeralNode of int literal
  | OpApplNode of op_appl_node
  | StringNode of string literal
  | SubstInNode of subst_in_node
  | TheoremDefRef of int
  | AssumeDefRef of int

and expr_or_op_arg =
  | Expression of expression
  | OpArg of int

and bound_symbol = {
  symbol_refs : int list;
  is_tuple : bool;
  expression : expression
}

and symbol =
  | Unbound of unbound_symbol
  | Bound of bound_symbol

and user_defined_op_kind = {
  node        : node;
  name        : string;
  arity       : int;
  precomments : string option;
  body        : expression;
  params      : leibniz_param list;
  recursive   : bool;
  local       : bool;
}

and assume_prove_node = {
  node        : node;
  assumptions : assumption_kind list;
  prove       : expression;
}

and assume_prove_like =
  | AssumeProveNode of assume_prove_node
  | AssumeProveSubstitution of subst_in_node

and new_symbol_node = {
  node        : node;
  symbol_ref  : int;
  domain      : expression option;
}

and assumption_kind =
  | Expression of expression
  | AssumeProveLike of assume_prove_like
  | NewSymbol of new_symbol_node

and expr_or_assume_prove =
  | Expression of expression
  | AssumeProveLike of assume_prove_like
[@@deriving show]

let rec xml_to_symbols (xml : tree) : symbol =
  match xml with
  | Node ("unbound", children) -> Unbound (xml_to_unbound_symbol children)
  | Node ("bound", children) -> Bound (xml_to_bound_symbol children)
  | _ -> conversion_failure __FUNCTION__ xml

and xml_to_bound_symbol (children : tree list) : bound_symbol =
  let rec consume_symbol_refs (acc : int list) (children : tree list) : int list * tree list =
    match children with
    | Node ("FormalParamNodeRef", [Node ("UID", [IValue symbol_ref])]) :: rest ->
      consume_symbol_refs (symbol_ref :: acc) rest
    | _ -> (List.rev acc, children)
  in match consume_symbol_refs [] children with
  | symbol_refs, [Node ("tuple", _); expression] -> {
      symbol_refs;
      is_tuple = true;
      expression = xml_to_expression expression;
    }
  | symbol_refs, [expression] -> {
      symbol_refs;
      is_tuple = false;
      expression = xml_to_expression expression;
    }
  | _ -> ls_conversion_failure __FUNCTION__ children

and xml_to_expr_or_op_arg (xml : tree) : expr_or_op_arg =
  match xml with
  | Node ("OpArgNode", children) -> (
    match extract_inline_node children with
    | node, [Node ("argument", [argument])] -> OpArg (get_ref argument)
    | _ -> conversion_failure __FUNCTION__ xml
  )
  | _ -> Expression (xml_to_expression xml)

and xml_to_op_appl_node (children : tree list) : op_appl_node =
  match extract_inline_node children with
  | node, [Node ("operator", [ref_node]); Node ("operands", operands); Node ("boundSymbols", bound_symbols)] -> {
      node;
      operator = get_ref ref_node;
      operands = List.map xml_to_expr_or_op_arg operands;
      bound_symbols = List.map xml_to_symbols bound_symbols;
    }
  | node, [Node ("operator", [ref_node]); Node ("operands", operands)] -> {
    node;
    operator = get_ref ref_node;
    operands = List.map xml_to_expr_or_op_arg operands;
    bound_symbols = []
  }
  | _ -> ls_conversion_failure __FUNCTION__ children

and xml_to_let_in_node (children : tree list) : let_in_node =
  match extract_inline_node children with
  | node, [Node ("body", [body]); Node ("opDefs", op_defs)]-> {
      node;
      body = xml_to_expression body;
      def_refs = List.map get_ref op_defs;
    }
  | _ -> ls_conversion_failure __FUNCTION__ children

(** TODO: there are more fields to parse in this structure
*)
and xml_to_at_node (children : tree list) : at_node =
  match extract_inline_node children with
  | node, _ -> {node}

and xml_to_label_node (children : tree list) : label_node =
  match extract_inline_node children with
  | node, [
    Node ("uniquename", [SValue name]);
    Node ("arity", [IValue arity]);
    Node ("body", [body]);
    Node ("params", parameters)
    ] -> {
      node;
      name;
      arity;
      body = xml_to_expr_or_assume_prove body;
      parameters = List.map get_ref parameters;
    }
  | _ -> ls_conversion_failure __FUNCTION__ children

and xml_to_assume_prove_node (children : tree list) : assume_prove_node =
  match extract_inline_node children with
  | node, Node ("assumes", assumptions) :: Node ("prove", [prove]) :: _ -> {
    node;
    assumptions = List.map xml_to_assumption_kind assumptions;
    prove = xml_to_expression prove;
  }
  | _ -> ls_conversion_failure __FUNCTION__ children

and xml_to_assumption_kind (xml : tree) : assumption_kind =
  match xml with
  | Node ("AssumeProveNode", children) -> AssumeProveLike (AssumeProveNode (xml_to_assume_prove_node children))
  | Node ("NewSymbNode", children) -> NewSymbol (xml_to_new_symbol_node children)
  | expr -> Expression (xml_to_expression expr)

and xml_to_new_symbol_node (children : tree list) : new_symbol_node =
  match extract_inline_node children with
  | node, [Node ("OpDeclNodeRef", [Node ("UID", [IValue symbol_ref])])] -> {
    node;
    symbol_ref;
    domain = None;
  }
  | node, [Node ("OpDeclNodeRef", [Node ("UID", [IValue symbol_ref])]); domain] -> {
    node;
    symbol_ref;
    domain = Some (xml_to_expression domain);
  }
  | _ -> ls_conversion_failure __FUNCTION__ children

and xml_to_expr_or_assume_prove (xml : tree) : expr_or_assume_prove =
  match xml with
  | Node ("AssumeProveNode", children) -> AssumeProveLike (AssumeProveNode (xml_to_assume_prove_node children))
  | Node ("APSubstInNode", children) -> AssumeProveLike (AssumeProveSubstitution (xml_to_subst_in_node children))
  | expr -> Expression (xml_to_expression expr)

and xml_to_substitution (xml : tree) : substitution =
  match xml with
  | Node ("Subst", [Node ("OpDeclNodeRef", [Node ("UID", [IValue target_uid])]); substitute]) -> {
      target_uid;
      substitute = xml_to_expr_or_op_arg substitute;
    }
  | _ -> conversion_failure __FUNCTION__ xml

and xml_to_subst_in_node (children : tree list) : subst_in_node =
  match extract_inline_node children with
  | node, [
    Node ("substs", substitutions);
    Node ("body", [body]);
    Node ("instFrom", [Node ("ModuleNodeRef", [Node ("UID", [IValue instance_from_mule_ref])])]);
    Node ("instTo", [Node ("ModuleNodeRef", [Node ("UID", [IValue instance_to_mule_ref])])])] -> {
      node;
      substitutions = List.map xml_to_substitution substitutions;
      body = xml_to_expression body;
      instance_from_mule_ref;
      instance_to_mule_ref
    }
  | _ -> ls_conversion_failure __FUNCTION__ children

and xml_to_expression (xml : tree) : expression =
  match xml with
  | Node ("AtNode", children) -> AtNode (xml_to_at_node children)
  | Node ("DecimalNode", children) -> DecimalNode (xml_to_decimal_node children)
  | Node ("LabelNode", children) -> LabelNode (xml_to_label_node children)
  | Node ("LetInNode", children) -> LetInNode (xml_to_let_in_node children)
  | Node ("NumeralNode", children) -> NumeralNode (xml_to_numeral_node children)
  | Node ("OpApplNode", children) -> OpApplNode (xml_to_op_appl_node children)
  | Node ("StringNode", children) -> StringNode (xml_to_string_node children)
  | Node ("SubstInNode", children) -> SubstInNode (xml_to_subst_in_node children)
  | Node ("TheoremDefRef", [Node ("UID", [IValue uid])]) -> TheoremDefRef uid
  | Node ("AssumeDefRef", [Node ("UID", [IValue uid])]) -> AssumeDefRef uid
  | _ -> conversion_failure __FUNCTION__ xml

and xml_to_user_defined_op_kind (children : tree list) : user_defined_op_kind =
  let node, name, arity, precomments, children = match extract_inline_node children with
  | node, Node ("uniquename", [SValue name]) :: Node ("arity", [IValue arity]) :: Node ("pre-comments", [SValue precomments]) :: children -> 
    node, name, arity, Some precomments, children
  | node, Node ("uniquename", [SValue name]) :: Node ("arity", [IValue arity]) :: children -> 
    node, name, arity, None, children
  | _ -> ls_conversion_failure __FUNCTION__ children
  in match children with
  | Node ("body", [body]) :: Node ("params", parameters) :: flags -> {
      node;
      name;
      arity;
      precomments;
      body        = xml_to_expression body;
      params      = List.map xml_to_leibniz_param parameters;
      recursive   = flags |> List.exists (is_tag "recursive");
      local       = flags |> List.exists (is_tag "local");
    }
  | _ -> ls_conversion_failure __FUNCTION__ children

[@@deriving show]

type instance_node = {
  node          : node;
  name          : string option;
  module_name   : string;
  substitutions : substitution list;
  parameters    : int list;
  local         : bool;
}
[@@deriving show]

let xml_to_instance_node (children : tree list) : instance_node =
  let extract_inline_name_opt (node, children : node * tree list) : (node * string option * tree list) =
    match children with
    | Node ("uniquename", [SValue name]) :: children -> (node, Some name, children)
    | _ -> (node, None, children)
  in match children |> extract_inline_node |> extract_inline_name_opt with
  | node, name, Node ("module", [SValue module_name]) :: Node ("substs", substitutions) :: Node ("params", params) :: local -> {
    node;
    name;
    module_name;
    substitutions = List.map xml_to_substitution substitutions;
    parameters = List.map get_ref params;
    local = match local with | [Node ("local", _)] -> true | _ -> false;
  }
  | _ -> ls_conversion_failure __FUNCTION__ children

(** This is a weird case that is almost definitely just a bug on SANY's side.
    For some reason SANY treats DEFINE M == INSTANCE Naturals proof steps
    differently from any other INSTANCE node, which always are either
    immediately inlined as M!-prefixed operators (in LET/IN blocks) or given
    as an InstanceNode type. This is the ModuleInstanceKind node type, which
    cannot even represent parameterization or substitution. In fact, it does
    not even export the name of the instance at all! Thankfully very few
    proofs seem to include DEFINE steps with an INSTANCE.

    TODO: fix this on SANY's side.
*)
let xml_to_define_step_instance_node (children : tree list) : instance_node =
  match extract_inline_node children with
  | node, Node ("uniquename", [SValue name]) :: local -> {
    node;
    name = Some name;
    module_name = "";
    substitutions = [];
    parameters = [];
    local = match local with | [Node ("local", _)] -> true | _ -> false;
  }
  | _ -> ls_conversion_failure __FUNCTION__ children

type use_or_hide_node = {
  node      : node;
  facts     : expression list;
  def_refs  : int list;
  only      : bool;
  hide      : bool;
}
[@@deriving show]

let xml_to_use_or_hide_node (children : tree list) : use_or_hide_node =
  match extract_inline_node children with
  | node, Node ("facts", facts) :: Node ("defs", defs) :: children ->
    let (only, hide) = match children with
    | [Node ("only", _); Node ("hide", _)] -> (true, true)
    | [Node ("only", _)] -> (true, false)
    | [Node ("hide", _)] -> (false, true)
    | [] -> (false, false)
    | _ -> ls_conversion_failure __FUNCTION__ children
    in {
      node;
      facts = List.map xml_to_expression facts;
      def_refs = List.map get_ref defs;
      only;
      hide;
    }
  | _ -> ls_conversion_failure __FUNCTION__ children

type unit_kind =
| Ref of int
| Instance of instance_node
| UseOrHide of use_or_hide_node
[@@deriving show]

type module_node = {
  node  : node;
  name  : string;
  extends : string list;
  units : unit_kind list;
}
[@@deriving show]

let xml_to_module_node (children : tree list) : module_node =
  let extract_extends (xml : tree) : string =
    match xml with
    | Node ("uniquename", [SValue name]) -> name
    | _ -> conversion_failure __FUNCTION__ xml
  in let ref_child child =
    match get_ref_opt child with
    | Some uid -> Ref uid
    | None -> match child with
      | Node ("InstanceNode", children) -> Instance (xml_to_instance_node children)
      | Node ("UseOrHideNode", children) -> UseOrHide (xml_to_use_or_hide_node children)
      | _ -> conversion_failure __FUNCTION__ child
  in match extract_inline_node children with
  | node, Node ("uniquename", [SValue name]) :: Node ("extends", extends) :: units -> {
    node;
    name;
    extends = List.map extract_extends extends;
    units = List.map ref_child units
  }
  | _ -> ls_conversion_failure __FUNCTION__ children

type declaration_kind =
  | Constant
  | Variable
  | BoundSymbol
  | NewConstant
  | NewVariable
  | NewState
  | NewAction
  | NewTemporal
[@@deriving show]

let xml_to_declaration_kind (kind : int) : declaration_kind =
  match kind with
  | 2 -> Constant
  | 3 -> Variable
  | 4 -> BoundSymbol
  | 24 -> NewConstant
  | 25 -> NewVariable
  | 26 -> NewState
  | 27 -> NewAction
  | 28 -> NewTemporal
  | _ -> conversion_failure __FUNCTION__ (IValue kind)

type op_decl_node = {
  node  : node;
  name  : string;
  arity : int;
  kind  : declaration_kind;
}
[@@deriving show]

let xml_to_op_decl_node (children : tree list) : op_decl_node =
  match extract_inline_node children with
  | node, [Node ("uniquename", [SValue name]); Node ("arity", [IValue arity]); Node ("kind", [IValue kind])] -> {
      node;
      name;
      arity;
      kind = xml_to_declaration_kind kind;
    }
  | _ -> ls_conversion_failure __FUNCTION__ children

type built_in_operator =
  (* Reserved words *)
  | TRUE
  | FALSE
  | BOOLEAN
  | STRING
  (* Prefix operators *)
  | LogicalNegation
  | UNION
  | SUBSET
  | DOMAIN
  | ENABLED
  | UNCHANGED
  | Always
  | Eventually
  (* Postfix operators *)
  | Prime
  (* Infix operators *)
  | SetIn
  | SetNotIn
  | Implies
  | Equivalent
  | Conjunction
  | Disjunction
  | Equals
  | NotEquals
  | SetMinus
  | Union
  | Intersect
  | SubsetEq
  | LeadsTo
  | ActionComposition
  | PlusArrow
  (* Language operators *)
  | FiniteSetLiteral
  | TupleLiteral
  | ConjunctionList
  | DisjunctionList
  | CartesianProduct
  | WeakFairness
  | StrongFairness
  | BoundedChoose
  | UnboundedChoose
  | ActionOrStutter
  | ActionNoStutter
  | BoundedExists
  | BoundedForAll
  | UnboundedExists
  | UnboundedForAll
  | TemporalExists
  | TemporalForAll
  | FiniteSetMap
  | FiniteSetFilter
  | FunctionSet
  | FunctionConstructor
  | FunctionDefinition
  | RecursiveFunctionDefinition
  | FunctionApplication
  | RecordSet
  | RecordConstructor
  | RecordSelect
  | Except
  | IfThenElse
  | Case
  | Subexpression
  | Pair
  | Sequence
  | CaseProofStep
  | PickProofStep
  | TakeProofStep
  | HaveProofStep
  | WitnessProofStep
  | SufficesProofStep
  | QedProofStep
[@@deriving show]

let xml_to_built_in_operator (name : string) : built_in_operator =
  match name with
  | "TRUE" -> TRUE
  | "FALSE" -> FALSE
  | "BOOLEAN" -> BOOLEAN
  | "STRING" -> STRING
  | "\\lnot" -> LogicalNegation
  | "UNION" -> UNION
  | "SUBSET" -> SUBSET
  | "DOMAIN" -> DOMAIN
  | "ENABLED" -> ENABLED
  | "UNCHANGED" -> UNCHANGED
  | "[]" -> Always
  | "<>" -> Eventually
  | "'" -> Prime
  | "\\in" -> SetIn
  | "\\notin" -> SetNotIn
  | "=>" -> Implies
  | "\\equiv" -> Equivalent
  | "\\land" -> Conjunction
  | "\\lor" -> Disjunction
  | "=" -> Equals
  | "/=" -> NotEquals
  | "\\" -> SetMinus
  | "\\union" -> Union
  | "\\intersect" -> Intersect
  | "\\subseteq" -> SubsetEq
  | "~>" -> LeadsTo
  | "\\cdot" -> ActionComposition
  | "-+->" -> PlusArrow
  | "$SetEnumerate" -> FiniteSetLiteral
  | "$Tuple" -> TupleLiteral
  | "$ConjList" -> ConjunctionList
  | "$DisjList" -> DisjunctionList
  | "$CartesianProd" -> CartesianProduct
  | "$WF" -> WeakFairness
  | "$SF" -> StrongFairness
  | "$BoundedChoose" -> BoundedChoose
  | "$UnboundedChoose" -> UnboundedChoose
  | "$SquareAct" -> ActionOrStutter
  | "$AngleAct" -> ActionNoStutter
  | "$BoundedExists" -> BoundedExists
  | "$BoundedForall" -> BoundedForAll
  | "$UnboundedExists" -> UnboundedExists
  | "$UnboundedForall" -> UnboundedForAll
  | "$TemporalExists" -> TemporalExists
  | "$TemporalForall" -> TemporalForAll
  | "$SetOfAll" -> FiniteSetMap
  | "$SubsetOf" -> FiniteSetFilter
  | "$SetOfFcns" -> FunctionSet
  | "$FcnConstructor" -> FunctionConstructor
  | "$NonRecursiveFcnSpec" -> FunctionDefinition
  | "$RecursiveFcnSpec" -> RecursiveFunctionDefinition
  | "$FcnApply" -> FunctionApplication
  | "$SetOfRcds" -> RecordSet
  | "$RcdConstructor" -> RecordConstructor
  | "$RcdSelect" -> RecordSelect
  | "$Except" -> Except
  | "$IfThenElse" -> IfThenElse
  | "$Case" -> Case
  | "$Nop" -> Subexpression
  | "$Pfcase" -> CaseProofStep
  | "$Pick" -> PickProofStep
  | "$Take" -> TakeProofStep
  | "$Have" -> HaveProofStep
  | "$Witness" -> WitnessProofStep
  | "$Suffices" -> SufficesProofStep
  | "$Qed" -> QedProofStep
  | "$Pair" -> Pair
  | "$Seq" -> Sequence
  | name -> conversion_failure __FUNCTION__ (SValue name)

type built_in_kind = {
  node       : node;
  operator   : built_in_operator;
  arity      : int;
  params     : leibniz_param list;
}
[@@deriving show]

let xml_to_built_in_kind (children : tree list) : built_in_kind =
  let node, name, arity, params = match extract_inline_node children with
    | node, [Node ("uniquename", [SValue name]); Node ("arity", [IValue arity]); Node ("params", params)] ->
        node, name, arity, List.map xml_to_leibniz_param params
    | node, [Node ("uniquename", [SValue name]); Node ("arity", [IValue arity])] ->
        node, name, arity, []
    | _ -> ls_conversion_failure __FUNCTION__ children
  in {
    node;
    operator = xml_to_built_in_operator name;
    arity;
    params
  }

type assume_def_node = {
  node        : node;
  name        : string;
  body        : expr_or_assume_prove;
}
[@@deriving show]

let xml_to_assume_def_node (children : tree list) : assume_def_node =
  match extract_inline_node children with
  | node, [Node ("uniquename", [SValue name]); body] -> {
    node;
    name;
    body = xml_to_expr_or_assume_prove body;
  }
  | _ -> ls_conversion_failure __FUNCTION__ children

type assume_node = {
  node        : node;
  definition  : int option;
  body        : expression;
}
[@@deriving show]

let xml_to_assume_node (children : tree list) : assume_node =
  match children |> extract_inline_node |> extract_inline_definition_opt with
  | node, definition, [Node ("body", [body])] -> {
    node;
    definition;
    body = xml_to_expression body;
  }
  | _ -> ls_conversion_failure __FUNCTION__ children

type theorem_def_node = {
  node        : node;
  name        : string;
  body        : expr_or_assume_prove;
}
[@@deriving show]

let xml_to_theorem_def_node (children : tree list) : theorem_def_node =
  match extract_inline_node children with
  | node, [Node ("uniquename", [SValue name]); body] -> {
    node;
    name;
    body = xml_to_expr_or_assume_prove body
  }
| _ -> ls_conversion_failure __FUNCTION__ children

type by_proof_node = {
  node  : node;
  facts : expression list;
  defs  : int list;
  only  : bool;
}
[@@deriving show]

let xml_to_by_proof_node (children : tree list) : by_proof_node =
  match extract_inline_node children with
  | node, Node ("facts", facts) :: Node ("defs", defs) :: children -> {
    node;
    facts = List.map xml_to_expression facts;
    defs = List.filter_map get_ref_opt defs;
    only = match children with | [Node ("only", _)] -> true | _ -> false
  }
  | _ -> ls_conversion_failure __FUNCTION__ children

type def_proof_step = {
  node      : node;
  def_refs  : int list;
}
[@@deriving show]

let xml_to_def_proof_step (children : tree list) : def_proof_step =
  match extract_inline_node children with
  | node, defs -> {
    node;
    def_refs = List.map get_ref defs;
  }

type proof_step_group =
  | TheoremNodeRef of int
  | DefStep of def_proof_step
  | UseOrHide of use_or_hide_node
  | InstanceNode of instance_node
  | TheoremNode
[@@deriving show]

type steps_proof_node = {
  node  : node;
  proof_level : int;
  steps : proof_step_group list;
}
[@@deriving show]

let xml_to_steps_proof_node (children : tree list) : steps_proof_node =
  let xml_to_proof_step_group xml =
    match xml with
    | Node ("TheoremNodeRef", [Node ("UID", [IValue uid])]) -> TheoremNodeRef uid
    | Node ("DefStepNode", children) -> DefStep (xml_to_def_proof_step children)
    | Node ("UseOrHideNode", children) -> UseOrHide (xml_to_use_or_hide_node children)
    | Node ("InstanceNode", children) -> InstanceNode (xml_to_instance_node children)
    | _ -> conversion_failure __FUNCTION__ xml
  in match extract_inline_node children with
  | node, Node ("proofLevel", [IValue proof_level]) :: steps -> {
      node;
      proof_level;
      steps = List.map xml_to_proof_step_group steps
    }
  | _ -> ls_conversion_failure __FUNCTION__ children

type proof_node_group =
  | Omitted of node
  | Obvious of node
  | By of by_proof_node
  | Steps of steps_proof_node
[@@deriving show]

type theorem_node = {
  node        : node;
  definition  : int option;
  body        : expr_or_assume_prove;
  proof       : proof_node_group option;
}
[@@deriving show]

let xml_to_theorem_node (children : tree list) : theorem_node =
  let xml_to_inline_proof_node_group (children : tree list) : proof_node_group option =
    match children with
    | Node ("omitted", children)  :: _ -> let (node, _) = extract_inline_node children in Some (Omitted node)
    | Node ("obvious", children)  :: _ -> let (node, _) = extract_inline_node children in Some (Obvious node)
    | Node ("by", children)       :: _ -> Some (By (xml_to_by_proof_node children))
    | Node ("steps", children)    :: _ -> Some (Steps (xml_to_steps_proof_node children))
    | [] -> None
    | _ -> ls_conversion_failure __FUNCTION__ children
  in match children |> extract_inline_node |> extract_inline_definition_opt with
  | node, definition, Node ("body", [body]) :: proof -> {
      node;
      definition;
      body        = xml_to_expr_or_assume_prove body;
      proof       = xml_to_inline_proof_node_group proof;
    }
  | _ -> ls_conversion_failure __FUNCTION__ children

type entry_kind =
  | FormalParamNode of formal_param_node
  | ModuleNode of module_node
  | OpDeclNode of op_decl_node
  | AssumeNode of assume_node
  | ModuleInstanceKind of instance_node
  | UserDefinedOpKind of user_defined_op_kind
  | BuiltInKind of built_in_kind
  | TheoremNode of theorem_node
  | TheoremDefNode of theorem_def_node
  | AssumeDefNode of assume_def_node
[@@deriving show]

let xml_to_entry_kind (xml : tree) : entry_kind =
  match xml with
  | Node ("ModuleNode", children) -> ModuleNode (xml_to_module_node children)
  | Node ("AssumeNode", children) -> AssumeNode (xml_to_assume_node children)
  | Node ("AssumeDef", children)  -> AssumeDefNode (xml_to_assume_def_node children)
  | Node ("OpDeclNode", children) -> OpDeclNode (xml_to_op_decl_node children)
  | Node ("UserDefinedOpKind", children) -> UserDefinedOpKind (xml_to_user_defined_op_kind children)
  | Node ("BuiltInKind", children) -> BuiltInKind (xml_to_built_in_kind children)
  | Node ("FormalParamNode", children) -> FormalParamNode (xml_to_formal_param_node children)
  | Node ("ModuleInstanceKind", children) -> ModuleInstanceKind (xml_to_define_step_instance_node children)
  | Node ("TheoremDefNode", children) -> TheoremDefNode (xml_to_theorem_def_node children)
  | Node ("TheoremNode", children)-> TheoremNode (xml_to_theorem_node children)
  | _ -> conversion_failure __FUNCTION__ xml

type entry = {
  uid : int;
  kind : entry_kind;
}
[@@deriving show]

let xml_to_entry (xml : tree) : entry =
  match xml with
  | Node ("entry", [Node ("UID", [IValue uid]); entry]) -> {
      uid;
      kind = xml_to_entry_kind entry;
    }
  | _ -> conversion_failure __FUNCTION__ xml

type modules = {
  root_module: string;
  context: entry list;
  module_refs : int list;
}
[@@deriving show]

let xml_to_modules (xml : tree) : modules =
  match xml with
  | Node ("modules", children) -> (
    match children with
    | Node ("RootModule", [SValue root_module]) :: Node ("context", entries) :: modules -> {
      root_module;
      context = List.map xml_to_entry entries;
      module_refs = List.map get_ref modules;
    }
    | _ -> ls_conversion_failure __FUNCTION__ children)
  | _ -> conversion_failure __FUNCTION__ xml

let xml_to_ast (xml : tree) : (modules, (string option * string)) result =
  let prev_backtrace = Printexc.backtrace_status () in
  if Params.debugging "sany" then Printexc.record_backtrace true;
  try
    let modules = xml_to_modules xml in
    Printexc.record_backtrace prev_backtrace;
    Result.ok modules
  with Invalid_argument e ->
    let trace = Printexc.get_backtrace () in
    Printexc.record_backtrace prev_backtrace;
    Result.error (None, Printf.sprintf "%s\n%s" e trace)

let get_module_ast_xml (module_path : string) (stdlib_path : string) : (modules, (string option * string)) result =
  let ( >>= ) = Result.bind in
  (source_to_sany_xml_str module_path stdlib_path) >>= str_to_xml >>= xml_to_ast
