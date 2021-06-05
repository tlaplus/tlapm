(* Intermediate syntax-tree transformations.

These transformations are applicable
before conversion of identifiers to
positional indices.

The expansions include:
- expansion of tuply declarations
*)
type mule = Module.T.mule


val expand:
    mule -> mule
