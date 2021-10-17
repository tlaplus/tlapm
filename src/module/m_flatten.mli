(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

open M_t


val flatten :
  modctx -> mule -> Util.Coll.Ss.t ->
    (mule_ Property.wrapped * Util.Coll.Ss.t)
