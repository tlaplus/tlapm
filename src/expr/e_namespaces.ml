(* Mint fresh TLA+ identifiers to extend namespace. *)
open Property


(* Scheme 1: Planar coordinates

Fresh identifier based on location.
This is as done in coalescing.

Note that in coalescing only line numbers
are used, not also column numbers.

Two definitions can appear on the same
line, which implies that multiple
definitions of the same identifier can
appear on the same line. For example:

```
---- MODULE SideBySideDefs ----
A == LET x == 1 IN x   B == LET x == 2 IN x
===============================
```
*)
let mint_by_coordinate
        (basename: string)
        (filename: string)
        (line: int)
        (column: int):
            string =
    (* A similar idea was implemented inside
    the function `Coalesce.rename_with_loc`.
    *)
    Printf.sprintf "%s_line_%d_column_%d" basename line column


let mint_from_hint
        (name: Util.hint):
            Util.hint =
    (* Add line and column to name.

    Unchanged if no locus information.
    *)
    match Util.query_locus name with
    | None -> name
    | Some locus -> begin
        let filename = locus.file in
        let start = locus.start in
        match start with
            | Actual loc ->
                begin
                let string = mint_by_coordinate
                    name.core filename loc.line loc.col in
                string @@ name
                end
            | Dummy -> name
        end


(* Scheme 2: Incremental indexing per identifier.

The minimal integer >= start is appended to `basename`
that yields a fresh identifier (one not in
`used_identifiers`).

This scheme has been used for creating fresh
constants to substitute primed occurrences of
variables when expanding `ENABLED` into constant
quantification.
*)
let mint_by_min_free
        (basename: string)
        (start: int)
        (used_identifiers: string list):
            string =
    (* The code in this function is based on
    code in the function
    `E_action.normalize_lambda_signature`.
    *)
    let mk_id name i =
        Printf.sprintf "%s_%d" name i in
    let f i = List.mem
        (mk_id basename i) used_identifiers in
    let i = ref start in
    while (f !i) do
        i := !i + 1
    done;
    mk_id basename !i
