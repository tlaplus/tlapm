(* Writing and loading of modules.

   Copyright (C) 2008-2010  INRIA and Microsoft Corporation
*)
open M_t

type module_content = Channel of in_channel | String of string | Filesystem

val module_content_prop : module_content Property.pfuncs
val parse_file : ?clock:Timing.clock -> Util.hint -> mule
val store_module : ?clock:Timing.clock -> mule -> unit
val complete_load : ?clock:Timing.clock -> ?root:string -> modctx -> modctx
