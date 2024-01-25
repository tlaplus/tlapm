(*
 * encode/subst.ml --- expressions (substitution)
 *
 *
 * Copyright (C) 2022  INRIA and Microsoft Corporation
 *)

open Property
open Expr.T
open Expr.Subst

class map_encode = object (self: 'self)
  inherit map as super

  method expr scx oe =
    begin
      match oe.core with
      | Apply (op, []) ->
          self#expr scx op $$ oe
      | _ ->
          super#expr scx oe

    end |> map_pats (List.map (self#expr scx))

end

let subst = new map_encode
