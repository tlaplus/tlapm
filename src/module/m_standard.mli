(* Standard TLA+ modules.

Copyright (C) 2008-2010  INRIA and Microsoft Corporation
*)
open M_t


(* all TLAPM builtin operators, including TLA+ builtins *)
val tlapm: mule
(* natural numbers *)
val naturals: mule
(* integers *)
val integers: mule
(* real numbers *)
val reals: mule
(* sequences *)
val sequences: mule
(* TLC *)
val tlc: mule
(* the initial module context, constructed at startup *)
val initctx: modctx
