(*
 * sysconf.ml --- thin interface to POSIX.1 sysconf(2)
 *
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

val nprocs : ?default:int -> unit -> int;;
