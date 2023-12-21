(* Writing and loading of modules.

Copyright (C) 2008-2010  INRIA and Microsoft Corporation
*)
open M_t


val parse_file: ?clock:Timing.clock -> Util.hint -> mule
val store_module: ?clock:Timing.clock -> mule -> unit
val complete_load:
    ?clock:Timing.clock -> ?root:string -> modctx -> modctx
