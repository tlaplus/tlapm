(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)
open Util.Coll

open M_t;;

(* module/save.ml *)
val external_deps : mule_ Property.wrapped ->
    Hs.t * Hs.t * mule Sm.t;;

(* tlapm.ml *)
val schedule : modctx -> modctx * mule list;;
