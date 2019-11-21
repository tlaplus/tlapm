(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

open M_t;;

(* module/save.ml *)
val external_deps : mule_ Property.wrapped -> Util.Coll.Hs.t;;

(* tlapm.ml *)
val schedule : modctx -> modctx * mule list;;
