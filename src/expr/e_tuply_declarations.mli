(* Translation of tuple declarations to simpler expressions.

Example of a tuply declaration:

```tla
\E <<x, y>> \in A \X B:  x = y
```
*)
open E_t


val expand_tuply_declarations:
    expr -> expr
val tuplify_functions:
    expr -> expr
