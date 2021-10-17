(*
 * module/globalness.ml --- detect global operators
 *
 *
 * Copyright (C) 2008-2013  INRIA and Microsoft Corporation
 *)

open Property
open M_t
open Proof.T

let isglobal : unit pfuncs =
  Property.make "Module.Globalness.isglobal"

let is_global x = Property.has x isglobal

let globalize = object (self : 'self)
  inherit [unit] Proof.Visit.map as super
  method expr scx e = super#expr scx (assign e isglobal ())
  method hyp scx h = super#hyp scx (assign h isglobal ())
end

let globalness md =
  let iterfun = function
    | {core = Axiom (nm, e)} as mu -> assign ((Axiom (nm, globalize#expr
    ((), Deque.empty) e)) @@ mu) isglobal ()
    | {core = Theorem (nm, sq, a, p, b, c)} as mu ->
       let (_, sq) = globalize#sequent ((), Deque.empty) sq in
       assign (Theorem (nm,sq,a, p, b, c) @@
       mu) isglobal ()
    | mu -> mu
  in {md.core with body = (List.map iterfun md.core.body)} @@ md
