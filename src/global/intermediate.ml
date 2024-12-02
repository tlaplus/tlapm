(* Intermediate syntax-tree mappings.

These mappings need to occur after the
parser and before positional indexing.
*)
module Expr = Expr
(* module Refs = Subexpression_references *)
module Module = Module
module Tuply = Expr.Tuply_declarations


type mule = Module.T.mule


let expand_tuplys
        (tla_module: mule):
            mule =
    let visitor =
        object (self: 'self)
        inherit Module.Visit.deep_map
        inherit [unit]
            Expr.Visit.map_concrete
        (* dependencies of `super`:
        `Expr.Visit.map`
        `Proof.Visit.map`
        `M_visit.map`

        so `Expr.Visit.map_concrete` overrides
        the methods of `Expr.Visit.map`. *)

        method expr scx e =
            e
            |> Tuply.expand_tuply_declarations
            (* |> Tuply.tuplify_functions *)
            (* function tuplification requires
            first expanding subexpression references *)
        end in
    visitor#tla_module_root
        tla_module


let expand
        (module_tree: mule):
            mule =
    (* Expand tuplys. *)
    module_tree
    (* |> Refs.expand *)
    |> expand_tuplys
