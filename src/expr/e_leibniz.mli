(* Detect Leibniz positions in operators.

Copyright (C) 2008-2014  INRIA and Microsoft Corporation
*)
open E_t
open E_visit


val is_leibniz: 'a Property.wrapped -> int -> bool

class virtual leibniz_visitor: [unit] E_visit.map
