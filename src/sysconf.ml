(*
 * sysconf.ml --- thin interface to POSIX.1 sysconf(2)
 *
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)
external nprocs_internal      : unit -> int = "sysconf_nprocs"

let nprocs ?(default=0) () =
  try nprocs_internal () with _ -> default
