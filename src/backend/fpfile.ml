(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

(* Each version of the fingerprint file format has its own module here.
   DO NOT EVER CHANGE THE MODULES DEFINED HERE.  You must define a new
   module for each new format.
*)

Revision.f "$Rev$";;

open Ext;;

module V1 = struct

  (* introduced on 2010-09-13 in r19028 *)
  (* NOTE: Cooper's results are buggy in this version *)

  type meth =
  | Isabelle of string
  | Zenon of zenon
  | Smt
  | Cooper
  | Sorry
  | Fail

  and zenon = {
    zenon_timeout : float;
    zenon_fallback : meth;
  }
  ;;

  type status_type =
  | Trivial
  | BeingProved
  | Success of meth
  | RFail of meth
  | Checked
  | Interrupted of meth
  ;;

  type tbl = (string, status_type list) Hashtbl.t;;
  (* The key is the MD5 converted to hex. *)

  (* File format:
     - magic number as a marshalled integer = 20101013
     - Fpver1 of string * string * tbl
                 (* zenon version, isabelle version, table *)
  *)

end;;


module V2 = struct

  (* introduced on 2010-11-19 in r19799 *)
  (* Adds type sti to have the date and version strings attached
     to each result instead of the whole table. *)
  (* NOTE: Cooper's results are buggy in this version *)

  type meth =
  | Isabelle of string
  | Zenon of zenon
  | Smt
  | Cooper
  | Sorry
  | Fail

  and zenon = {
    zenon_timeout : float;
    zenon_fallback : meth;
  }
  ;;

  type status_type =
  | Trivial
  | BeingProved
  | Success of meth
  | RFail of meth
  | Checked
  | Interrupted of meth
  ;;

  type date = int * int * int * int * int * int;;
  (* year, month-1, day, hour, minute, second *)

  type sti = status_type * date * string * string * string;;
             (* status, date, pm version, zenon version, isabelle version *)

  type tbl = (string, sti list) Hashtbl.t;;
  (* The key is the MD5 converted to hex. *)

  (* File format:
     - magic number as a marshalled integer = 20101013
     - Fpver2 of tbl
  *)

end;;


module V3 = struct

  (* introduced on 2010-11-30 in r20012 *)
  (* Same as V2, but Cooper's results are OK. *)

  type meth =
  | Isabelle of string
  | Zenon of zenon
  | Smt
  | Cooper
  | Sorry
  | Fail

  and zenon = {
    zenon_timeout : float;
    zenon_fallback : meth;
  }
  ;;

  type status_type =
  | Trivial
  | BeingProved
  | Success of meth
  | RFail of meth
  | Checked
  | Interrupted of meth
  ;;

  type date = int * int * int * int * int * int;;
  (* year, month-1, day, hour, minute, second *)

  type sti = status_type * date * string * string * string;;
             (* status, date, pm version, zenon version, isabelle version *)

  type tbl = (string, sti list) Hashtbl.t;;
  (* The key is the MD5 converted to hex. *)

  (* File format:
     - magic number as a marshalled integer = 20101013
     - Fpver3 of tbl
  *)

end;;


module V4 = struct

  (* introduced on 2011-04-11 in r21224 *)
  (* Adds timeout to Isabelle method. *)

  type floatomega = F of float | Omega;;

  type meth =
  | Isabelle of isabelle
  | Zenon of zenon
  | Smt
  | Cooper
  | Sorry
  | Fail

  and zenon = {
    zenon_timeout : float;
    zenon_fallback : meth;
  }

  and isabelle = {
    isabelle_timeout : floatomega;
    isabelle_tactic : string;
  }
  ;;

  type status_type =
  | Trivial
  | BeingProved
  | Success of meth
  | RFail of meth
  | Checked
  | Interrupted of meth
  ;;

  type date = int * int * int * int * int * int;;
  (* year, month-1, day, hour, minute, second *)

  type sti = status_type * date * string * string * string;;
             (* status, date, pm version, zenon version, isabelle version *)

  type tbl = (string, sti list) Hashtbl.t;;
  (* The key is the MD5 converted to hex. *)

  (* File format:
     - magic number as a marshalled integer = 20101013
     - Fpver4 of tbl
  *)

end;;


module V5 = struct

  (* introduced on 2011-04-22 in r21326 *)
  (* Adds the "reason" type and corresponding field in "sti". *)
  (* Adds incremental saving of the fingerprints at the end of the file. *)

  type floatomega = F of float | Omega;;

  type meth =
  | Isabelle of isabelle
  | Zenon of zenon
  | Smt
  | Cooper
  | Sorry
  | Fail

  and zenon = {
    zenon_timeout : float;
    zenon_fallback : meth;
  }

  and isabelle = {
    isabelle_timeout : floatomega;
    isabelle_tactic : string;
  }
  ;;

  type status_type =
  | Trivial
  | BeingProved
  | Success of meth
  | RFail of meth
  | Checked
  | Interrupted of meth
  ;;

  type reason =
  | False
  | Timeout
  ;;

  type date = int * int * int * int * int * int;;
  (* year, month-1, day, hour, minute, second *)

  type sti = status_type * reason option * date * string * string * string
             (* status, reason for failure, date,
                pm version, zenon version, isabelle version *)

  type tbl = (string, sti list) Hashtbl.t;;
  (* The key is the MD5 converted to hex. *)

  (* File format:
     - magic number as a marshalled integer = 20101013
     - Fpver5 of tbl
     - any number of (Digest.t, sti list) pairs
  *)

end;;


module V6 = struct

  module V6a = struct

    (* introduced on 2011-04-26 in r21333 *)
    (* Breaks status_type in two types and pushes reason into the
       RFail case of status_type_aux.
       Also adds type str to replace sti list.
     *)

    type floatomega = F of float | Omega;;

    type meth =
    | Isabelle of isabelle
    | Zenon of zenon
    | Smt
    | Cooper
    | Sorry
    | Fail

    and zenon = {
      zenon_timeout : float;
      zenon_fallback : meth;
    }

    and isabelle = {
      isabelle_timeout : floatomega;
      isabelle_tactic : string;
    }
    ;;

    type reason =
    | False
    | Timeout
    ;;

    type status_type_aux =
    | RSucc
    | RFail of reason option
    | RInt
    ;;

    type status_type =
    | Triv
    | NTriv of status_type_aux * meth
    ;;

    type date = int * int * int * int * int * int;;
    (* year, month-1, day, hour, minute, second *)

    type sti = status_type * date * string * string * string;;
               (* status, date, pm version, zenon version, isabelle version *)

    type str = {
      tres : sti option;
      zres : sti option;
      ires : sti option;
      smtres : sti option;
      cooperres : sti option;
    };;

    type tbl = (string, str) Hashtbl.t;;
    (* The key is the MD5 converted to hex. *)

    (* File format:
       - magic number as a marshalled integer = 20101013
       - Fpver6 of tbl
       - any number of (Digest.t, sti list) pairs
    *)

  end;;

  module V6b = struct

    (* introduced on 2011-05-02 in r21418 *)
    (* Adds Yices method. *)
    (* NOTE: adding Yices made the types incompatible, but the version
       number was not changed.
     *)

    type floatomega = F of float | Omega;;

    type meth =
    | Isabelle of isabelle
    | Zenon of zenon
    | Smt
    | Yices
    | Cooper
    | Sorry
    | Fail

    and zenon = {
      zenon_timeout : float;
      zenon_fallback : meth;
    }

    and isabelle = {
      isabelle_timeout : floatomega;
      isabelle_tactic : string;
    }
    ;;

    type reason =
    | False
    | Timeout
    ;;

    type status_type_aux =
    | RSucc
    | RFail of reason option
    | RInt
    ;;

    type status_type =
    | Triv
    | NTriv of status_type_aux * meth
    ;;

    type date = int * int * int * int * int * int;;
    (* year, month-1, day, hour, minute, second *)

    type sti = status_type * date * string * string * string;;
               (* status, date, pm version, zenon version, isabelle version *)

    type str = {
      tres : sti option;
      zres : sti option;
      ires : sti option;
      smtres : sti option;
      cooperres : sti option;
    };;

    type tbl = (string, str) Hashtbl.t;;
    (* The key is the MD5 converted to hex. *)

    (* File format:
       - magic number as a marshalled integer = 20101013
       - Fpver6 of tbl
       - any number of (Digest.t, sti list) pairs
    *)

  end;;

  (* Least common denominator of V6a and V6b *)

  type floatomega = F of float | Omega;;

  type meth =
  | Isabelle of isabelle
  | Zenon of zenon
  | Smt
  | Unusable1
  | Unusable2
  | Unusable3
  | Fail

  and zenon = {
    zenon_timeout : float;
    zenon_fallback : meth;
  }

  and isabelle = {
    isabelle_timeout : floatomega;
    isabelle_tactic : string;
  }
  ;;

  type reason =
  | False
  | Timeout
  ;;

  type status_type_aux =
  | RSucc
  | RFail of reason option
  | RInt
  ;;

  type status_type =
  | Triv
  | NTriv of status_type_aux * meth
  ;;

  type date = int * int * int * int * int * int;;
  (* year, month-1, day, hour, minute, second *)

  type sti = status_type * date * string * string * string;;
             (* status, date, pm version, zenon version, isabelle version *)

  type str = {
    tres : sti option;
    zres : sti option;
    ires : sti option;
    smtres : sti option;
    cooperres : sti option;
  };;

  type tbl = (string, str) Hashtbl.t;;
  (* The key is the MD5 converted to hex. *)

  (* File format:
     - magic number as a marshalled integer = 20101013
     - Fpver6 of tbl
     - any number of (Digest.t, sti list) pairs
  *)

end;;

module V7 = struct

  (* introduced on 2011-05-09 in r21621 *)
  (* Adds case "Cantwork" to type reason.
     Also adds "yres" field to type str.
   *)

  type floatomega = F of float | Omega;;

  type meth =
  | Isabelle of isabelle
  | Zenon of zenon
  | Smt
  | Yices
  | Cooper
  | Sorry
  | Fail

  and zenon = {
    zenon_timeout : float;
    zenon_fallback : meth;
  }

  and isabelle = {
    isabelle_timeout : floatomega;
    isabelle_tactic : string;
  }
  ;;

  type reason =
  | False
  | Timeout
  | Cantwork of string
  ;;

  type status_type_aux =
  | RSucc
  | RFail of reason option
  | RInt
  ;;

  type status_type =
  | Triv
  | NTriv of status_type_aux * meth
  ;;

  type date = int * int * int * int * int * int;;
  (* year, month-1, day, hour, minute, second *)

  type sti = status_type * date * string * string * string;;
             (* status, date, pm version, zenon version, isabelle version *)

  type str = {
    tres : sti option;
    zres : sti option;
    ires : sti option;
    smtres : sti option;
    cooperres : sti option;
    yres : sti option;
  };;

  type tbl = (string, str) Hashtbl.t;;
  (* The key is the MD5 converted to hex. *)

  (* File format:
     - magic number as a marshalled integer = 20101013
     - Fpver7 of tbl
     - any number of (Digest.t, sti list) pairs
  *)

end;;

module V8 = struct

  module V8a = struct

    (* introduced on 2011-06-14 in r21946 *)
    (* Adds cases "SmtT" and "YicesT" to type meth. *)

    type floatomega = F of float | Omega;;

    type meth =
    | Isabelle of isabelle
    | Zenon of zenon
    | Smt
    | SmtT of floatomega
    | Yices
    | YicesT of floatomega
    | Cooper
    | Sorry
    | Fail

    and zenon = {
      zenon_timeout : float;
      zenon_fallback : meth;
    }

    and isabelle = {
      isabelle_timeout : floatomega;
      isabelle_tactic : string;
    }
    ;;

    type reason =
    | False
    | Timeout
    | Cantwork of string
    ;;

    type status_type_aux =
    | RSucc
    | RFail of reason option
    | RInt
    ;;

    type status_type =
    | Triv
    | NTriv of status_type_aux * meth
    ;;

    type date = int * int * int * int * int * int;;
    (* year, month-1, day, hour, minute, second *)

    type sti = status_type * date * string * string * string;;
               (* status, date, pm version, zenon version, isabelle version *)

    type str = {
      tres : sti option;
      zres : sti option;
      ires : sti option;
      smtres : sti option;
      cooperres : sti option;
      yres : sti option;
    };;

    type tbl = (string, str) Hashtbl.t;;
    (* The key is the MD5 converted to hex. *)

    (* File format:
       - magic number as a marshalled integer = 20101013
       - Fpver8 of tbl
       - any number of (Digest.t, sti list) pairs
    *)

  end;;

  module V8b = struct

    (* introduced on 2011-10-03 in r23936 *)
    (* Adds cases "Z3" and "Z3T" to type meth.
       Also adds field "z3res" to type str.
       NOTE: adding Z3 and Z3T made the types incompatible, but the version
       number was not changed.
     *)

    type floatomega = F of float | Omega;;

    type meth =
    | Isabelle of isabelle
    | Zenon of zenon
    | Smt
    | SmtT of floatomega
    | Yices
    | YicesT of floatomega
    | Z3
    | Z3T of floatomega
    | Cooper
    | Sorry
    | Fail

    and zenon = {
      zenon_timeout : float;
      zenon_fallback : meth;
    }

    and isabelle = {
      isabelle_timeout : floatomega;
      isabelle_tactic : string;
    }
    ;;

    type reason =
    | False
    | Timeout
    | Cantwork of string
    ;;

    type status_type_aux =
    | RSucc
    | RFail of reason option
    | RInt
    ;;

    type status_type =
    | Triv
    | NTriv of status_type_aux * meth
    ;;

    type date = int * int * int * int * int * int;;
    (* year, month-1, day, hour, minute, second *)

    type sti = status_type * date * string * string * string;;
               (* status, date, pm version, zenon version, isabelle version *)

    type str = {
      tres : sti option;
      zres : sti option;
      ires : sti option;
      smtres : sti option;
      cooperres : sti option;
      yres : sti option;
      z3res : sti option;
    };;

    type tbl = (string, str) Hashtbl.t;;
    (* The key is the MD5 converted to hex. *)

    (* File format:
       - magic number as a marshalled integer = 20101013
       - Fpver8 of tbl
       - any number of (Digest.t, sti list) pairs
    *)

  end;;

  (* Least common denominator of V8a and V8b *)

  type floatomega = F of float | Omega;;

  type meth =
  | Isabelle of isabelle
  | Zenon of zenon
  | Smt
  | SmtT of floatomega
  | Yices
  | YicesT of floatomega
  | Unusable1
  | Z3T of floatomega
  | Unusable2
  | Unusable3
  | Fail

  and zenon = {
    zenon_timeout : float;
    zenon_fallback : meth;
  }

  and isabelle = {
    isabelle_timeout : floatomega;
    isabelle_tactic : string;
  }
  ;;

  type reason =
  | False
  | Timeout
  | Cantwork of string
  ;;

  type status_type_aux =
  | RSucc
  | RFail of reason option
  | RInt
  ;;

  type status_type =
  | Triv
  | NTriv of status_type_aux * meth
  ;;

  type date = int * int * int * int * int * int;;
  (* year, month-1, day, hour, minute, second *)

  type sti = status_type * date * string * string * string;;
             (* status, date, pm version, zenon version, isabelle version *)

  type str = {
    tres : sti option;
    zres : sti option;
    ires : sti option;
    smtres : sti option;
    cooperres : sti option;
    yres : sti option;
  };;

  type tbl = (string, str) Hashtbl.t;;
  (* The key is the MD5 converted to hex. *)

  (* File format:
     - magic number as a marshalled integer = 20101013
     - Fpver8 of tbl
     - any number of (Digest.t, sti list) pairs
  *)

end;;

module V9 = struct

  (* introduced on 2011-10-15 in r24180 *)
  (* Adds case "Ccv3T" to type meth.
     Also adds field "cvc3res" to type str.
   *)

  type floatomega = F of float | Omega;;

  type meth =
  | Isabelle of isabelle
  | Zenon of zenon
  | Smt
  | SmtT of floatomega
  | Yices
  | YicesT of floatomega
  | Z3
  | Z3T of floatomega
  | Cooper
  | Sorry
  | Fail
  | Cvc3T of floatomega

  and zenon = {
    zenon_timeout : float;
    zenon_fallback : meth;
  }

  and isabelle = {
    isabelle_timeout : floatomega;
    isabelle_tactic : string;
  }
  ;;

  type reason =
  | False
  | Timeout
  | Cantwork of string
  ;;

  type status_type_aux =
  | RSucc
  | RFail of reason option
  | RInt
  ;;

  type status_type =
  | Triv
  | NTriv of status_type_aux * meth
  ;;

  type date = int * int * int * int * int * int;;
  (* year, month-1, day, hour, minute, second *)

  type sti = status_type * date * string * string * string;;
             (* status, date, pm version, zenon version, isabelle version *)

  type str = {
    tres : sti option;
    zres : sti option;
    ires : sti option;
    smtres : sti option;
    cooperres : sti option;
    yres : sti option;
    z3res : sti option;
    cvc3res : sti option;
  };;

  type tbl = (string, str) Hashtbl.t;;
  (* The key is the MD5 converted to hex. *)

  (* File format:
     - magic number as a marshalled integer = 20101013
     - Fpver9 of tbl
     - any number of (Digest.t, sti list) pairs
  *)

end;;

module V10 = struct

  (* introduced on 2011-11-30 in r24863 *)
  (* Adds cases "Smt2lib" and "Smt2z3" to type meth.
     Also adds fields "smt2libres" and "smt2z3res" to type str.
   *)

  type floatomega = F of float | Omega;;

  type meth =
  | Isabelle of isabelle
  | Zenon of zenon
  | Smt
  | SmtT of floatomega
  | Yices
  | YicesT of floatomega
  | Z3
  | Z3T of floatomega
  | Cooper
  | Sorry
  | Fail
  | Cvc3T of floatomega
  | Smt2lib of floatomega
  | Smt2z3 of floatomega

  and zenon = {
    zenon_timeout : float;
    zenon_fallback : meth;
  }

  and isabelle = {
    isabelle_timeout : floatomega;
    isabelle_tactic : string;
  }
  ;;

  type reason =
  | False
  | Timeout
  | Cantwork of string
  ;;

  type status_type_aux =
  | RSucc
  | RFail of reason option
  | RInt
  ;;

  type status_type =
  | Triv
  | NTriv of status_type_aux * meth
  ;;

  type date = int * int * int * int * int * int;;
  (* year, month-1, day, hour, minute, second *)

  type sti = status_type * date * string * string * string;;
             (* status, date, pm version, zenon version, isabelle version *)

  type str = {
    tres : sti option;
    zres : sti option;
    ires : sti option;
    smtres : sti option;
    cooperres : sti option;
    yres : sti option;
    z3res : sti option;
    cvc3res : sti option;
    smt2libres : sti option;
    smt2z3res : sti option;
  };;

  type tbl = (string, str) Hashtbl.t;;
  (* The key is the MD5 converted to hex. *)

  (* File format:
     - magic number as a marshalled integer = 20101013
     - Fpver10 of tbl
     - any number of (Digest.t, sti list) pairs
  *)

  let version = 10;;

end;;

module V11 = struct

  (* introduced on 2012-10-16 in r29003 *)
  (* Adds cases "Smt3", "Z33", "Cvc33", "Yices3", "Verit", "Spass", "Tptp"
     to type meth.
     Previous SMT methods (Smt, Yices, Z3, Cvc3, SmtSmt2lib, Smt2z3) should
     be deprecated.
   *)

  type floatomega = F of float | Omega;;

  type meth =
  | Isabelle of isabelle
  | Zenon of zenon
  | Smt
  | SmtT of floatomega
  | Yices
  | YicesT of floatomega
  | Z3
  | Z3T of floatomega
  | Cooper
  | Sorry
  | Fail
  | Cvc3T of floatomega
  | Smt2lib of floatomega
  | Smt2z3 of floatomega
  | Smt3 of floatomega
  | Z33 of floatomega
  | Cvc33 of floatomega
  | Yices3 of floatomega
  | Verit of floatomega
  | Spass of floatomega
  | Tptp of floatomega

  and zenon = {
    zenon_timeout : float;
    zenon_fallback : meth;
  }

  and isabelle = {
    isabelle_timeout : floatomega;
    isabelle_tactic : string;
  }
  ;;

  type reason =
  | False
  | Timeout
  | Cantwork of string
  ;;

  type status_type_aux =
  | RSucc
  | RFail of reason option
  | RInt
  ;;

  type status_type =
  | Triv
  | NTriv of status_type_aux * meth
  ;;

  type date = int * int * int * int * int * int;;
  (* year, month-1, day, hour, minute, second *)

  type sti = status_type * date * string * string * string;;
             (* status, date, pm version, zenon version, isabelle version *)

  type str = {
    tres : sti option;
    zres : sti option;
    ires : sti option;
    smtres : sti option;
    cooperres : sti option;
    yres : sti option;
    z3res : sti option;
    cvc3res : sti option;
    smt2libres : sti option;
    smt2z3res : sti option;
    smt3res : sti option;
    z33res : sti option;
    cvc33res : sti option;
    yices3res : sti option;
    veritres : sti option;
    spassres : sti option;
    tptpres : sti option;
  };;

  type tbl = (string, str) Hashtbl.t;;
  (* The key is the MD5 converted to hex. *)

  (* File format:
     - magic number as a marshalled integer = 20101013
     - Fpver11 of tbl
     - any number of (Digest.t, sti list) pairs
  *)

  let version = 11;;

end;;

module V12 = struct

  (* introduced on 2013-08-26 in r32535 *)
  (* Adds case "LS4"
     to type meth.
   *)

  type floatomega = F of float | Omega;;

  type meth =
  | Isabelle of isabelle
  | Zenon of zenon
  | Smt
  | SmtT of floatomega
  | Yices
  | YicesT of floatomega
  | Z3
  | Z3T of floatomega
  | Cooper
  | Sorry
  | Fail
  | Cvc3T of floatomega
  | Smt2lib of floatomega
  | Smt2z3 of floatomega
  | Smt3 of floatomega
  | Z33 of floatomega
  | Cvc33 of floatomega
  | Yices3 of floatomega
  | Verit of floatomega
  | Spass of floatomega
  | Tptp of floatomega
  | LS4 of floatomega

  and zenon = {
    zenon_timeout : float;
    zenon_fallback : meth;
  }

  and isabelle = {
    isabelle_timeout : floatomega;
    isabelle_tactic : string;
  }
  ;;

  type reason =
  | False
  | Timeout
  | Cantwork of string
  ;;

  type status_type_aux =
  | RSucc
  | RFail of reason option
  | RInt
  ;;

  type status_type =
  | Triv
  | NTriv of status_type_aux * meth
  ;;

  type date = int * int * int * int * int * int;;
  (* year, month-1, day, hour, minute, second *)

  type sti = status_type * date * string * string * string;;
             (* status, date, pm version, zenon version, isabelle version *)

  type str = {
    tres : sti option;
    zres : sti option;
    ires : sti option;
    smtres : sti option;
    cooperres : sti option;
    yres : sti option;
    z3res : sti option;
    cvc3res : sti option;
    smt2libres : sti option;
    smt2z3res : sti option;
    smt3res : sti option;
    z33res : sti option;
    cvc33res : sti option;
    yices3res : sti option;
    veritres : sti option;
    spassres : sti option;
    tptpres : sti option;
    ls4res : sti option;
  };;

  type tbl = (string, str) Hashtbl.t;;
  (* The key is the MD5 converted to hex. *)

  (* File format:
     - magic number as a marshalled integer = 20101013
     - Fpver12 of tbl
     - any number of (Digest.t, sti list) pairs
  *)

  let version = 12;;

end;;

module V13 = struct

  (* introduced on 2019- in revision *)
  (* Adds the cases "ExpandENABLED", "ExpandCdot", "AutoUSE", "Lambdify",
     "ENABLEDaxioms", "LevelComparison"
     to type meth.
   *)

  type floatomega = F of float | Omega;;

  type meth =
  | Isabelle of isabelle
  | Zenon of zenon
  | Smt
  | SmtT of floatomega
  | Yices
  | YicesT of floatomega
  | Z3
  | Z3T of floatomega
  | Cooper
  | Sorry
  | Fail
  | Cvc3T of floatomega
  | Smt2lib of floatomega
  | Smt2z3 of floatomega
  | Smt3 of floatomega
  | Z33 of floatomega
  | Cvc33 of floatomega
  | Yices3 of floatomega
  | Verit of floatomega
  | Spass of floatomega
  | Tptp of floatomega
  | LS4 of floatomega
  | ExpandENABLED
  | AutoUSE  (* as needed for expanding `ENABLED` and `\cdot` *)
  | ExpandCdot
  | Lambdify
  | ENABLEDaxioms
  | LevelComparison
  | Trivial

  and zenon = {
    zenon_timeout : float;
    zenon_fallback : meth;
  }

  and isabelle = {
    isabelle_timeout : floatomega;
    isabelle_tactic : string;
  }
  ;;

  type reason =
  | False
  | Timeout
  | Cantwork of string
  ;;

  type status_type_aux =
  | RSucc
  | RFail of reason option
  | RInt
  ;;

  type status_type =
  | Triv
  | NTriv of status_type_aux * meth
  ;;

  type date = int * int * int * int * int * int;;
  (* year, month-1, day, hour, minute, second *)

  type sti = status_type * date * string * string * string;;
             (* status, date, pm version, zenon version, isabelle version *)

  type str = {
    tres : sti option;
    zres : sti option;
    ires : sti option;
    smtres : sti option;
    cooperres : sti option;
    yres : sti option;
    z3res : sti option;
    cvc3res : sti option;
    smt2libres : sti option;
    smt2z3res : sti option;
    smt3res : sti option;
    z33res : sti option;
    cvc33res : sti option;
    yices3res : sti option;
    veritres : sti option;
    spassres : sti option;
    tptpres : sti option;
    ls4res : sti option;
    expandenabledres : sti option;
    expandcdotres : sti option;
    lambdifyres: sti option;
    enabledaxiomsres: sti option;
    levelcomparisonres: sti option;
  };;

  type tbl = (string, str) Hashtbl.t;;
  (* The key is the MD5 converted to hex. *)

  (* File format:
     - magic number as a marshalled integer = 20101013
     - Fpver13 of tbl
     - any number of (Digest.t, sti list) pairs
  *)

  let version = 13;;

end;;

type fp =
  | FP1 of string * string * V1.tbl
  | FP2 of V2.tbl
  | FP3 of V3.tbl
  | FP4 of V4.tbl
  | FP5 of V5.tbl
  | FP6 of V6.tbl
  | FP7 of V7.tbl
  | FP8 of V8.tbl
  | FP9 of V9.tbl
  | FP10 of V10.tbl
  | FP11 of V11.tbl
  | FP12 of V12.tbl
  | FP13 of V13.tbl
  | FPunknown of unit
;;


(* Note: the above modules and types are strictly private to this
   file and their contents must not escape from this module.
   Likewise, external types must not get into the above modules.
 *)

(* ===================================================================== *)

let myrevision = "$Rev$";;

open Printf;;
open V13;;

let fptbl = ref (Hashtbl.create 500 : V13.tbl);;

let magic_number = 20101013;;

let write_fp_table oc =
  output_value oc magic_number;
  output_value oc (FP13 !fptbl);
;;

let get_date month_offset =
  let tm = Unix.localtime (Unix.gettimeofday ()) in
  (1900 + tm.Unix.tm_year, 1 + tm.Unix.tm_mon + month_offset, tm.Unix.tm_mday,
   tm.Unix.tm_hour, tm.Unix.tm_min, tm.Unix.tm_sec)
;;

let hist_dir_name = ref "";;

module FN = Filename;;

let fp_init fp_file sources =
  let histdir = fp_file ^ ".history" in
  hist_dir_name := histdir;
  let (y, m, d, hr, mi, se) = get_date 0 in
  let date = Printf.sprintf "%04d-%02d-%02d_%02d_%02d_%02d" y m d hr mi se in
  let destdir = FN.concat histdir date in

  (* Save context and "before" version of FP. *)
  let tlasources = List.map (fun x -> x ^ ".tla") sources in
  let sourcefiles = String.concat " " (List.map FN.quote tlasources) in
  ignore (Sys.command ("mkdir -p " ^ FN.quote destdir));
  ignore (Sys.command ("cp -p " ^ FN.quote fp_file ^ " " ^ sourcefiles
                       ^ " " ^ FN.quote destdir ^ " 2>/dev/null"));

  (* Remove saved stuff beyond the 10th *)
  let hist_subdirs = FN.concat (FN.quote histdir) "*" in
  ignore (Sys.command ("rm -rf `ls -1td " ^ hist_subdirs ^ "| tail -n +11`"));

  (* Open FP file for writing and output the old fingerprints. *)
  let oc = open_out_bin fp_file in
  write_fp_table oc;
  oc
;;

module T = Types;;
module M = Method;;

(* Vx means the latest version, currently V13 *)

let rec st6_to_Vx st =
  match st with
  | T.Triv -> Triv
  | T.NTriv (sta, meth) -> NTriv (sta6_to_Vx sta, meth_to_Vx meth)

and sta6_to_Vx sta =
  match sta with
  | T.RSucc -> RSucc
  | T.RFail None -> RFail None
  | T.RFail (Some r) -> RFail (Some (reason_to_Vx r))
  | T.RInt -> RInt

and reason_to_Vx r =
  match r with
  | T.False -> False
  | T.Timeout -> Timeout
  | T.Cantwork s -> Cantwork s

and meth_to_Vx m =
  match m with
  | M.Isabelle (tmo, tac) ->
     Isabelle {isabelle_timeout = floatomega_to_Vx tmo; isabelle_tactic = tac}
  | M.Zenon tmo -> Zenon {zenon_timeout = tmo; zenon_fallback = Fail}
  | M.SmtT tmo -> SmtT (floatomega_to_Vx tmo)
  | M.YicesT tmo -> YicesT (floatomega_to_Vx tmo)
  | M.Z3T tmo -> Z3T (floatomega_to_Vx tmo)
  | M.Cooper -> Cooper
  | M.Fail -> Fail
  | M.Cvc3T tmo -> Cvc3T (floatomega_to_Vx tmo)
  | M.Smt2lib tmo -> Smt2lib (floatomega_to_Vx tmo)
  | M.Smt2z3 tmo -> Smt2z3 (floatomega_to_Vx tmo)
  | M.Smt3 tmo -> Smt3 (floatomega_to_Vx tmo)
  | M.Z33 tmo -> Z33 (floatomega_to_Vx tmo)
  | M.Cvc33 tmo -> Cvc33 (floatomega_to_Vx tmo)
  | M.Yices3 tmo -> Yices3 (floatomega_to_Vx tmo)
  | M.Verit tmo -> Verit (floatomega_to_Vx tmo)
  | M.Spass tmo -> Spass (floatomega_to_Vx tmo)
  | M.Tptp tmo -> Tptp (floatomega_to_Vx tmo)
  | M.LS4 tmo -> LS4 (floatomega_to_Vx tmo)
  | M.ExpandENABLED -> ExpandENABLED
  | M.AutoUSE -> AutoUSE
  | M.ExpandCdot -> ExpandCdot
  | M.Lambdify -> Lambdify
  | M.ENABLEDaxioms -> ENABLEDaxioms
  | M.LevelComparison -> LevelComparison
  | M.Trivial -> Trivial

and floatomega_to_Vx f = F f;;

let fp_to_Vx fp = fp;;
(* V13 fingerprints are hex-encoded digests, as are external fingerprints.
   Future versions will use raw digests, hence the need for this translation
   function.
*)

let date_to_Vx d = d;;
(* V13 dates use month-1, as do external dates.  Future versions will use
   month, hence the need for this translation function. *)

type prover =
  | Pisabelle of string
  | Pzenon
  | Psmt
  | Pyices
  | Pz3
  | Pcooper
  | Psorry
  | Pfail
  | Pcvc3
  | Psmt2lib
  | Psmt2z3
  | Psmt3
  | Pz33
  | Pcvc33
  | Pyices3
  | Pverit
  | Pspass
  | Ptptp
  | Pls4
  | Pexpandenabled
  | Pautouse
  | Pexpandcdot
  | Plambdify
  | Penabledaxioms
  | Plevelcomparison
  | Ptrivial
;;

let prover_of_method m =
  match m with
  | Isabelle {isabelle_tactic = tac} -> Pisabelle tac
  | Zenon _ -> Pzenon
  | Smt | SmtT _ -> Psmt
  | Yices | YicesT _ -> Pyices
  | Z3 | Z3T _ -> Pz3
  | Cooper -> Pcooper
  | Sorry -> Psorry
  | Fail -> Pfail
  | Cvc3T _ -> Pcvc3
  | Smt2lib _ -> Psmt2lib
  | Smt2z3 _ -> Psmt2z3
  | Smt3 _ -> Psmt3
  | Z33 _ -> Pz33
  | Cvc33 _ -> Pcvc33
  | Yices3 _ -> Pyices3
  | Verit _ -> Pverit
  | Spass _ -> Pspass
  | Tptp _ -> Ptptp
  | LS4 _ -> Pls4
  | ExpandENABLED -> Pexpandenabled
  | ExpandCdot -> Pexpandcdot
  | AutoUSE -> Pautouse
  | Lambdify -> Plambdify
  | ENABLEDaxioms -> Penabledaxioms
  | LevelComparison -> Plevelcomparison
  | Trivial -> Ptrivial
;;

let normalize m =
  match m with
  | Isabelle {isabelle_timeout = Omega; isabelle_tactic = t} ->
     Isabelle {isabelle_timeout = F infinity; isabelle_tactic = t}
  | Zenon {zenon_timeout = tmo; zenon_fallback = _} ->
     Zenon {zenon_timeout = tmo; zenon_fallback = Fail}
  | Smt | SmtT (Omega) -> SmtT (F infinity)
  | Yices | YicesT (Omega) -> YicesT (F infinity)
  | Z3 | Z3T (Omega) -> Z3T (F infinity)
  | Cvc3T (Omega) -> Cvc3T (F infinity)
  | Smt2lib (Omega) -> Smt2lib (F infinity)
  | Smt2z3 (Omega) -> Smt2z3 (F infinity)
  | Smt3 (Omega) -> Smt3 (F infinity)
  | Z33 (Omega) -> Z33 (F infinity)
  | Cvc33 (Omega) -> Cvc33 (F infinity)
  | Yices3 (Omega) -> Yices3 (F infinity)
  | Verit (Omega) -> Verit (F infinity)
  | Spass (Omega) -> Spass (F infinity)
  | Tptp (Omega) -> Tptp (F infinity)
  | LS4 (Omega) -> LS4 (F infinity)
  | _ -> m
;;

let get_timeout m =
  match m with
  | Isabelle {isabelle_timeout = F t}
  | Zenon {zenon_timeout = t}
  | SmtT (F t)
  | YicesT (F t)
  | Z3T (F t)
  | Cvc3T (F t)
  | Smt2lib (F t)
  | Smt2z3 (F t)
  | Smt3 (F t)
  | Z33 (F t)
  | Cvc33 (F t)
  | Yices3 (F t)
  | Verit (F t)
  | Spass (F t)
  | Tptp (F t)
  | LS4 (F t)
  -> t
  | _ -> infinity
;;

(* Arbitrary order on the methods, and inside each method the best result
   is greater. *)
(* FIXME this is slightly broken (as was the previous code) because
   isabelle results are compared without regard for the tactic field.
   It will become easy to fix when we change to a list of results instead
   of a record.
 *)
let order st1 st2 =
  let (r1, _, _, _, _) = st1 in
  let (r2, _, _, _, _) = st2 in
  match r1, r2 with
  | Triv, Triv -> 0
  | Triv, _ -> 1
  | _, Triv -> -1
  | NTriv (r1, m1), NTriv (r2, m2)
    when prover_of_method m1 = prover_of_method m2 ->
     begin match r1, r2 with
     | RSucc, RFail _ -> 1
     | RFail _, RSucc -> -1
     | RInt, _ -> -1
     | _, RInt -> 1
     | RSucc, RSucc -> compare (get_timeout m2) (get_timeout m1)
     | RFail _, RFail _ -> compare (get_timeout m1) (get_timeout m2)
     end
  | NTriv (_, m1), NTriv (_, m2) -> compare (normalize m1) (normalize m2)
;;

let opt_to_list o =
  match o with
  | None -> []
  | Some x -> [x]
;;

let record_to_list r =
  List.flatten [
    opt_to_list r.tres;
    opt_to_list r.zres;
    opt_to_list r.ires;
    opt_to_list r.smtres;
    opt_to_list r.cooperres;
    opt_to_list r.yres;
    opt_to_list r.z3res;
    opt_to_list r.cvc3res;
    opt_to_list r.smt2libres;
    opt_to_list r.smt2z3res;
    opt_to_list r.smt3res;
    opt_to_list r.z33res;
    opt_to_list r.cvc33res;
    opt_to_list r.yices3res;
    opt_to_list r.veritres;
    opt_to_list r.spassres;
    opt_to_list r.tptpres;
    opt_to_list r.ls4res;
  ]
;;

let empty = {
  tres = None;
  zres = None;
  ires = None;
  smtres = None;
  cooperres = None;
  yres = None;
  z3res = None;
  cvc3res = None;
  smt2libres = None;
  smt2z3res = None;
  smt3res = None;
  z33res = None;
  cvc33res = None;
  yices3res = None;
  veritres = None;
  spassres = None;
  tptpres = None;
  ls4res = None;
  expandenabledres = None;
  expandcdotres = None;
  lambdifyres = None;
  enabledaxiomsres = None;
  levelcomparisonres = None;
};;

let add_to_record r st =
  let (x, _, _, _, _) = st in
  match x with
  | Triv -> {r with tres = Some st}
  | NTriv (_, Isabelle _) -> {r with ires = Some st}
  | NTriv (_, Zenon _) -> {r with zres = Some st}
  | NTriv (_, (Smt | SmtT _)) -> {r with smtres = Some st}
  | NTriv (_, (Yices | YicesT _)) -> {r with yres = Some st}
  | NTriv (_, (Z3 | Z3T _)) -> {r with z3res = Some st}
  | NTriv (_, Cooper) -> {r with cooperres = Some st}
  | NTriv (_, Cvc3T _) -> {r with cvc3res = Some st}
  | NTriv (_, Smt2lib _) -> {r with smt2libres = Some st}
  | NTriv (_, Smt2z3 _) -> {r with smt2z3res = Some st}
  | NTriv (_, Smt3 _) -> {r with smt3res = Some st}
  | NTriv (_, Z33 _) -> {r with z33res = Some st}
  | NTriv (_, Cvc33 _) -> {r with cvc33res = Some st}
  | NTriv (_, Yices3 _) -> {r with yices3res = Some st}
  | NTriv (_, Verit _) -> {r with veritres = Some st}
  | NTriv (_, Spass _) -> {r with spassres = Some st}
  | NTriv (_, Tptp _) -> {r with tptpres = Some st}
  | NTriv (_, LS4 _) -> {r with ls4res = Some st}
  | NTriv (_, ExpandENABLED) -> {r with expandenabledres = Some st}
  | NTriv (_, ExpandCdot) -> {r with expandcdotres = Some st}
  | NTriv (_, Lambdify) -> {r with lambdifyres = Some st}
  | NTriv (_, ENABLEDaxioms) -> {r with enabledaxiomsres = Some st}
  | NTriv (_, LevelComparison) -> {r with levelcomparisonres = Some st}
  | _ -> r
;;

let list_to_record l = List.fold_left add_to_record empty l;;

let add_to_table fp l1 =
  let r = try Hashtbl.find !fptbl fp with Not_found -> empty in
  let l2 = record_to_list r in
  let l = List.sort ~cmp:order (l1 @ l2) in
  Hashtbl.replace !fptbl fp (list_to_record l)
;;

let fp_writes
        (oc: out_channel)
        (fp: string)
        (results: Types.status_type6 list):
            unit =
  let fp: string = fp_to_Vx fp in
  let date = get_date (-1) in
  let zv = Params.get_zenon_verfp () in
  let iv = Params.get_isabelle_version () in
  let f (result: Types.status_type6) =
      (
          st6_to_Vx result,  (* : status_type6 *)
          date_to_Vx date,  (* = date *)
          Params.rawversion (),  (* : string = `tlapm` version *)
          zv,  (* : string = `zenon` version *)
          iv  (* : string = `isabelle` version *)
      )
    in
  let l = List.map f results in
  (* FIXME Triv results should not be sent back to server.ml, instead
     of propagating them all the way and then eliminating them here. *)
  let filt r =
    match r with
    | (Triv, _, _, _, _) -> false
    | (NTriv (_, Fail), _, _, _, _) -> false
    | _ -> true
  in
  let l = List.filter filt l in
  Marshal.to_channel oc (fp, l) [];
  flush oc;
  add_to_table fp l;
;;

let num_fingerprints_loaded = ref 0;;

let fp_close_and_consolidate file oc =
  close_out oc;
  let tmpfile = file ^ ".tmp" in
  let noc = open_out_bin tmpfile in
  write_fp_table noc;
  close_out noc;
  Sys.rename tmpfile file;
  Util.printf "(* fingerprints written in %S *)" file;
  if Hashtbl.length !fptbl < !num_fingerprints_loaded then begin
    Errors.err "The fingerprints file %s has fewer entries than its \
                previous version (stored in %s)." file !hist_dir_name;
  end;
;;

let add_v1 zv iv fp stl =
  let tr_fp x = x in
  let rec tr_method m =
    match m with
    | V1.Isabelle tac ->
       Isabelle {isabelle_timeout = F infinity; isabelle_tactic = tac}
    | V1.Zenon {V1.zenon_timeout = t; V1.zenon_fallback = mm} ->
       Zenon {zenon_timeout = t; zenon_fallback = tr_method mm}
    | V1.Smt -> SmtT (F infinity)
    | V1.Cooper -> failwith "buggy cooper"
    | V1.Sorry -> Sorry
    | V1.Fail -> Fail
  in
  let tr_st st =
    try match st with
    | V1.Trivial -> [Triv]
    | V1.Success m -> [NTriv (RSucc, tr_method m)]
    | V1.RFail m -> [NTriv (RFail None, tr_method m)]
    | V1.Interrupted m -> [NTriv (RInt, tr_method m)]
    | _ -> []
    with Failure _ -> []
  in
  let to_sti x = (x, (0, 0, 0, 0, 0, 0), "", zv, iv) in
  add_to_table (tr_fp fp) (List.map to_sti (List.flatten (List.map tr_st stl)))
;;

let add_v2 fp stil =
  let tr_fp x = x in
  let rec tr_method m =
    match m with
    | V2.Isabelle tac ->
       Isabelle {isabelle_timeout = F infinity; isabelle_tactic = tac}
    | V2.Zenon {V2.zenon_timeout = t; V2.zenon_fallback = mm} ->
       Zenon {zenon_timeout = t; zenon_fallback = tr_method mm}
    | V2.Smt -> SmtT (F infinity)
    | V2.Cooper -> failwith "buggy cooper"
    | V2.Sorry -> Sorry
    | V2.Fail -> Fail
  in
  let tr_st st =
    match st with
    | V2.Trivial -> Triv
    | V2.Success m -> NTriv (RSucc, tr_method m)
    | V2.RFail m -> NTriv (RFail None, tr_method m)
    | V2.Interrupted m -> NTriv (RInt, tr_method m)
    | _ -> failwith "tr_st"
  in
  let tr_sti (st, dt, pmv, zv, iv) =
    try [(tr_st st, dt, pmv, zv, iv)]
    with Failure _ -> []
  in
  add_to_table (tr_fp fp) (List.flatten (List.map tr_sti stil))
;;

let add_v3 fp stil =
  let tr_fp x = x in
  let rec tr_method m =
    match m with
    | V3.Isabelle tac ->
       Isabelle {isabelle_timeout = F infinity; isabelle_tactic = tac}
    | V3.Zenon {V3.zenon_timeout = t; V3.zenon_fallback = mm} ->
       Zenon {zenon_timeout = t; zenon_fallback = tr_method mm}
    | V3.Smt -> SmtT (F infinity);
    | V3.Cooper -> Cooper
    | V3.Sorry -> Sorry
    | V3.Fail -> Fail
  in
  let tr_st st =
    match st with
    | V3.Trivial -> Triv
    | V3.Success m -> NTriv (RSucc, tr_method m)
    | V3.RFail m -> NTriv (RFail None, tr_method m)
    | V3.Interrupted m -> NTriv (RInt, tr_method m)
    | _ -> failwith "tr_st"
  in
  let tr_sti (st, dt, pmv, zv, iv) =
    try [(tr_st st, dt, pmv, zv, iv)]
    with Failure _ -> []
  in
  add_to_table (tr_fp fp) (List.flatten (List.map tr_sti stil))
;;

let add_v4 fp stil =
  let tr_fp x = x in
  let tr_floatomega x =
    match x with
    | V4.F f -> F f
    | V4.Omega -> F infinity
  in
  let rec tr_method m =
    match m with
    | V4.Isabelle {V4.isabelle_timeout = tmo; V4.isabelle_tactic = tac} ->
       Isabelle {isabelle_timeout = tr_floatomega tmo; isabelle_tactic = tac}
    | V4.Zenon {V4.zenon_timeout = t; V4.zenon_fallback = mm} ->
       Zenon {zenon_timeout = t; zenon_fallback = tr_method mm}
    | V4.Smt -> SmtT (F infinity)
    | V4.Cooper -> Cooper
    | V4.Sorry -> Sorry
    | V4.Fail -> Fail
  in
  let tr_st st =
    match st with
    | V4.Trivial -> Triv
    | V4.Success m -> NTriv (RSucc, tr_method m)
    | V4.RFail m -> NTriv (RFail None, tr_method m)
    | V4.Interrupted m -> NTriv (RInt, tr_method m)
    | _ -> failwith "tr_st"
  in
  let tr_sti (st, dt, pmv, zv, iv) =
    try [(tr_st st, dt, pmv, zv, iv)]
    with Failure _ -> []
  in
  add_to_table (tr_fp fp) (List.flatten (List.map tr_sti stil))
;;

let add_v5 fp stil =
  let tr_fp x = x in
  let tr_floatomega x =
    match x with
    | V5.F f -> F f
    | V5.Omega -> F infinity
  in
  let rec tr_method m =
    match m with
    | V5.Isabelle {V5.isabelle_timeout = tmo; V5.isabelle_tactic = tac} ->
       Isabelle {isabelle_timeout = tr_floatomega tmo; isabelle_tactic = tac}
    | V5.Zenon {V5.zenon_timeout = t; V5.zenon_fallback = mm} ->
       Zenon {zenon_timeout = t; zenon_fallback = tr_method mm}
    | V5.Smt -> SmtT (F infinity);
    | V5.Cooper -> Cooper
    | V5.Sorry -> Sorry
    | V5.Fail -> Fail
  in
  let tr_reason_option x =
    match x with
    | None -> None
    | Some V5.False -> Some False
    | Some V5.Timeout -> Some Timeout
  in
  let tr_st st reason =
    match st with
    | V5.Trivial -> Triv
    | V5.Success m -> NTriv (RSucc, tr_method m)
    | V5.RFail m -> NTriv (RFail (tr_reason_option reason), tr_method m)
    | V5.Interrupted m -> NTriv (RInt, tr_method m)
    | _ -> failwith "tr_st"
  in
  let tr_sti (st, reason, dt, pmv, zv, iv) =
    try [(tr_st st reason, dt, pmv, zv, iv)]
    with Failure _ -> []
  in
  add_to_table (tr_fp fp) (List.flatten (List.map tr_sti stil))
;;

let add_v6l fp stil =
  let tr_fp x = x in
  let tr_floatomega x =
    match x with
    | V6.F f -> F f
    | V6.Omega -> F infinity
  in
  let rec tr_method m =
    match m with
    | V6.Isabelle {V6.isabelle_timeout = tmo; V6.isabelle_tactic = tac} ->
       Isabelle {isabelle_timeout = tr_floatomega tmo; isabelle_tactic = tac}
    | V6.Zenon {V6.zenon_timeout = t; V6.zenon_fallback = mm} ->
       Zenon {zenon_timeout = t; zenon_fallback = tr_method mm}
    | V6.Smt -> SmtT (F infinity)
    | V6.Unusable1 | V6.Unusable2 | V6.Unusable3 ->
       failwith "ambiguous method value"
    | V6.Fail -> Fail
  in
  let tr_reason_option x =
    match x with
    | None -> None
    | Some V6.False -> Some False
    | Some V6.Timeout -> Some Timeout
  in
  let tr_st st =
    match st with
    | V6.Triv -> Triv
    | V6.NTriv (V6.RSucc, m) -> NTriv (RSucc, tr_method m)
    | V6.NTriv (V6.RFail r, m) ->
       NTriv (RFail (tr_reason_option r), tr_method m)
    | V6.NTriv (V6.RInt, m) -> NTriv (RInt, tr_method m)
  in
  let tr_sti (st, dt, pmv, zv, iv) =
    try [(tr_st st, dt, pmv, zv, iv)]
    with Failure _ -> []
  in
  add_to_table (tr_fp fp) (List.flatten (List.map tr_sti stil))
;;

let add_v6r fp str =
  let tr_fp x = x in
  let option_to_list x =
    match x with
    | None -> []
    | Some x -> [x]
  in
  let str_to_list r =
    List.flatten [
      option_to_list r.V6.tres;
      option_to_list r.V6.zres;
      option_to_list r.V6.ires;
      option_to_list r.V6.smtres;
      option_to_list r.V6.cooperres;
    ]
  in
  add_v6l (tr_fp fp) (str_to_list str)
;;

let add_v7l fp stil =
  let tr_fp x = x in
  let tr_floatomega x =
    match x with
    | V7.F f -> F f
    | V7.Omega -> F infinity
  in
  let rec tr_method m =
    match m with
    | V7.Isabelle {V7.isabelle_timeout = tmo; V7.isabelle_tactic = tac} ->
       Isabelle {isabelle_timeout = tr_floatomega tmo; isabelle_tactic = tac}
    | V7.Zenon {V7.zenon_timeout = t; V7.zenon_fallback = mm} ->
       Zenon {zenon_timeout = t; zenon_fallback = tr_method mm}
    | V7.Smt -> SmtT (F infinity)
    | V7.Yices -> YicesT (F infinity)
    | V7.Cooper -> Cooper
    | V7.Sorry -> Sorry
    | V7.Fail -> Fail
  in
  let tr_reason_option x =
    match x with
    | None -> None
    | Some V7.False -> Some False
    | Some V7.Timeout -> Some Timeout
    | Some (V7.Cantwork s) -> Some (Cantwork s)
  in
  let tr_st st =
    match st with
    | V7.Triv -> Triv
    | V7.NTriv (V7.RSucc, m) -> NTriv (RSucc, tr_method m)
    | V7.NTriv (V7.RFail r, m) ->
       NTriv (RFail (tr_reason_option r), tr_method m)
    | V7.NTriv (V7.RInt, m) -> NTriv (RInt, tr_method m)
  in
  let tr_sti (st, dt, pmv, zv, iv) =
    try [(tr_st st, dt, pmv, zv, iv)]
    with Failure _ -> []
  in
  add_to_table (tr_fp fp) (List.flatten (List.map tr_sti stil))
;;

let add_v7r fp str =
  let tr_fp x = x in
  let option_to_list x =
    match x with
    | None -> []
    | Some x -> [x]
  in
  let str_to_list r =
    List.flatten [
      option_to_list r.V7.tres;
      option_to_list r.V7.zres;
      option_to_list r.V7.ires;
      option_to_list r.V7.smtres;
      option_to_list r.V7.cooperres;
      option_to_list r.V7.yres;
    ]
  in
  add_v7l (tr_fp fp) (str_to_list str)
;;

let add_v8l fp stil =
  let tr_fp x = x in
  let tr_floatomega x =
    match x with
    | V8.F f -> F f
    | V8.Omega -> F infinity
  in
  let rec tr_method m =
    match m with
    | V8.Isabelle {V8.isabelle_timeout = tmo; V8.isabelle_tactic = tac} ->
       Isabelle {isabelle_timeout = tr_floatomega tmo; isabelle_tactic = tac}
    | V8.Zenon {V8.zenon_timeout = t; V8.zenon_fallback = mm} ->
       Zenon {zenon_timeout = t; zenon_fallback = tr_method mm}
    | V8.Smt -> SmtT (F infinity)
    | V8.SmtT tmo -> SmtT (tr_floatomega tmo)
    | V8.Yices -> YicesT (F infinity)
    | V8.YicesT tmo -> YicesT (tr_floatomega tmo)
    | V8.Z3T tmo -> Z3T (tr_floatomega tmo)
    | V8.Unusable1 | V8.Unusable2 | V8.Unusable3 ->
       failwith "ambiguous method value"
    | V8.Fail -> Fail
  in
  let tr_reason_option x =
    match x with
    | None -> None
    | Some V8.False -> Some False
    | Some V8.Timeout -> Some Timeout
    | Some (V8.Cantwork s) -> Some (Cantwork s)
  in
  let tr_st st =
    match st with
    | V8.Triv -> Triv
    | V8.NTriv (V8.RSucc, m) -> NTriv (RSucc, tr_method m)
    | V8.NTriv (V8.RFail r, m) ->
       NTriv (RFail (tr_reason_option r), tr_method m)
    | V8.NTriv (V8.RInt, m) -> NTriv (RInt, tr_method m)
  in
  let tr_sti (st, dt, pmv, zv, iv) =
    try [(tr_st st, dt, pmv, zv, iv)]
    with Failure _ -> []
  in
  add_to_table (tr_fp fp) (List.flatten (List.map tr_sti stil))
;;

let add_v8r fp str =
  let tr_fp x = x in
  let option_to_list x =
    match x with
    | None -> []
    | Some x -> [x]
  in
  let str_to_list r =
    List.flatten [
      option_to_list r.V8.tres;
      option_to_list r.V8.zres;
      option_to_list r.V8.ires;
      option_to_list r.V8.smtres;
      option_to_list r.V8.cooperres;
      option_to_list r.V8.yres;
    ]
  in
  add_v8l (tr_fp fp) (str_to_list str)
;;

let add_v9l fp stil =
  let tr_fp x = x in
  let tr_floatomega x =
    match x with
    | V9.F f -> F f
    | V9.Omega -> F infinity
  in
  let rec tr_method m =
    match m with
    | V9.Isabelle {V9.isabelle_timeout = tmo; V9.isabelle_tactic = tac} ->
       Isabelle {isabelle_timeout = tr_floatomega tmo; isabelle_tactic = tac}
    | V9.Zenon {V9.zenon_timeout = t; V9.zenon_fallback = mm} ->
       Zenon {zenon_timeout = t; zenon_fallback = tr_method mm}
    | V9.Smt -> SmtT (F infinity)
    | V9.SmtT tmo -> SmtT (tr_floatomega tmo)
    | V9.Yices -> YicesT (F infinity)
    | V9.YicesT tmo -> YicesT (tr_floatomega tmo)
    | V9.Z3 -> Z3T (F infinity)
    | V9.Z3T tmo -> Z3T (tr_floatomega tmo)
    | V9.Cooper -> Cooper
    | V9.Sorry -> Sorry
    | V9.Fail -> Fail
    | V9.Cvc3T tmo -> Cvc3T (tr_floatomega tmo)
  in
  let tr_reason_option x =
    match x with
    | None -> None
    | Some V9.False -> Some False
    | Some V9.Timeout -> Some Timeout
    | Some (V9.Cantwork s) -> Some (Cantwork s)
  in
  let tr_st st =
    match st with
    | V9.Triv -> Triv
    | V9.NTriv (V9.RSucc, m) -> NTriv (RSucc, tr_method m)
    | V9.NTriv (V9.RFail r, m) ->
       NTriv (RFail (tr_reason_option r), tr_method m)
    | V9.NTriv (V9.RInt, m) -> NTriv (RInt, tr_method m)
  in
  let tr_sti (st, dt, pmv, zv, iv) =
    try [(tr_st st, dt, pmv, zv, iv)]
    with Failure _ -> []
  in
  add_to_table (tr_fp fp) (List.flatten (List.map tr_sti stil))
;;

let add_v9r fp str =
  let tr_fp x = x in
  let option_to_list x =
    match x with
    | None -> []
    | Some x -> [x]
  in
  let str_to_list r =
    List.flatten [
      option_to_list r.V9.tres;
      option_to_list r.V9.zres;
      option_to_list r.V9.ires;
      option_to_list r.V9.smtres;
      option_to_list r.V9.cooperres;
      option_to_list r.V9.yres;
      option_to_list r.V9.z3res;
      option_to_list r.V9.cvc3res;
    ]
  in
  add_v9l (tr_fp fp) (str_to_list str)
;;

let add_v10l fp stil =
  let tr_fp x = x in
  let tr_floatomega x =
    match x with
    | V10.F f -> F f
    | V10.Omega -> F infinity
  in
  let rec tr_method m =
    match m with
    | V10.Isabelle {V10.isabelle_timeout = tmo; V10.isabelle_tactic = tac} ->
       Isabelle {isabelle_timeout = tr_floatomega tmo; isabelle_tactic = tac}
    | V10.Zenon {V10.zenon_timeout = t; V10.zenon_fallback = mm} ->
       Zenon {zenon_timeout = t; zenon_fallback = tr_method mm}
    | V10.Smt -> SmtT (F infinity)
    | V10.SmtT tmo -> SmtT (tr_floatomega tmo)
    | V10.Yices -> YicesT (F infinity)
    | V10.YicesT tmo -> YicesT (tr_floatomega tmo)
    | V10.Z3 -> Z3T (F infinity)
    | V10.Z3T tmo -> Z3T (tr_floatomega tmo)
    | V10.Cooper -> Cooper
    | V10.Sorry -> Sorry
    | V10.Fail -> Fail
    | V10.Cvc3T tmo -> Cvc3T (tr_floatomega tmo)
    | V10.Smt2lib tmo -> Smt2lib (tr_floatomega tmo)
    | V10.Smt2z3 tmo -> Smt2z3 (tr_floatomega tmo)
  in
  let tr_reason_option x =
    match x with
    | None -> None
    | Some V10.False -> Some False
    | Some V10.Timeout -> Some Timeout
    | Some (V10.Cantwork s) -> Some (Cantwork s)
  in
  let tr_st st =
    match st with
    | V10.Triv -> Triv
    | V10.NTriv (V10.RSucc, m) -> NTriv (RSucc, tr_method m)
    | V10.NTriv (V10.RFail r, m) ->
       NTriv (RFail (tr_reason_option r), tr_method m)
    | V10.NTriv (V10.RInt, m) -> NTriv (RInt, tr_method m)
  in
  let tr_sti (st, dt, pmv, zv, iv) =
    try [(tr_st st, dt, pmv, zv, iv)]
    with Failure _ -> []
  in
  add_to_table (tr_fp fp) (List.flatten (List.map tr_sti stil))
;;

let add_v10r fp str =
  let tr_fp x = x in
  let option_to_list x =
    match x with
    | None -> []
    | Some x -> [x]
  in
  let str_to_list r =
    List.flatten [
      option_to_list r.V10.tres;
      option_to_list r.V10.zres;
      option_to_list r.V10.ires;
      option_to_list r.V10.smtres;
      option_to_list r.V10.cooperres;
      option_to_list r.V10.yres;
      option_to_list r.V10.z3res;
      option_to_list r.V10.cvc3res;
      option_to_list r.V10.smt2libres;
      option_to_list r.V10.smt2z3res;
    ]
  in
  add_v10l (tr_fp fp) (str_to_list str)
;;

let add_v11l fp stil =
  let tr_fp x = x in
  let tr_floatomega x =
    match x with
    | V11.F f -> F f
    | V11.Omega -> F infinity
  in
  let rec tr_method m =
    match m with
    | V11.Isabelle {V11.isabelle_timeout = tmo; V11.isabelle_tactic = tac} ->
       Isabelle {isabelle_timeout = tr_floatomega tmo; isabelle_tactic = tac}
    | V11.Zenon {V11.zenon_timeout = t; V11.zenon_fallback = mm} ->
       Zenon {zenon_timeout = t; zenon_fallback = tr_method mm}
    | V11.Smt -> SmtT (F infinity)
    | V11.SmtT tmo -> SmtT (tr_floatomega tmo)
    | V11.Yices -> YicesT (F infinity)
    | V11.YicesT tmo -> YicesT (tr_floatomega tmo)
    | V11.Z3 -> Z3T (F infinity)
    | V11.Z3T tmo -> Z3T (tr_floatomega tmo)
    | V11.Cooper -> Cooper
    | V11.Sorry -> Sorry
    | V11.Fail -> Fail
    | V11.Cvc3T tmo -> Cvc3T (tr_floatomega tmo)
    | V11.Smt2lib tmo -> Smt2lib (tr_floatomega tmo)
    | V11.Smt2z3 tmo -> Smt2z3 (tr_floatomega tmo)
    | V11.Smt3 tmo -> Smt2z3 (tr_floatomega tmo)
    | V11.Z33 tmo -> Z33 (tr_floatomega tmo)
    | V11.Cvc33 tmo -> Cvc33 (tr_floatomega tmo)
    | V11.Yices3 tmo ->Yices3 (tr_floatomega tmo)
    | V11.Verit tmo -> Verit (tr_floatomega tmo)
    | V11.Spass tmo -> Spass (tr_floatomega tmo)
    | V11.Tptp tmo -> Tptp (tr_floatomega tmo)
  in
  let tr_reason_option x =
    match x with
    | None -> None
    | Some V11.False -> Some False
    | Some V11.Timeout -> Some Timeout
    | Some (V11.Cantwork s) -> Some (Cantwork s)
  in
  let tr_st st =
    match st with
    | V11.Triv -> Triv
    | V11.NTriv (V11.RSucc, m) -> NTriv (RSucc, tr_method m)
    | V11.NTriv (V11.RFail r, m) ->
       NTriv (RFail (tr_reason_option r), tr_method m)
    | V11.NTriv (V11.RInt, m) -> NTriv (RInt, tr_method m)
  in
  let tr_sti (st, dt, pmv, zv, iv) =
    try [(tr_st st, dt, pmv, zv, iv)]
    with Failure _ -> []
  in
  add_to_table (tr_fp fp) (List.flatten (List.map tr_sti stil))
;;

let add_v11r fp str =
  let tr_fp x = x in
  let option_to_list x =
    match x with
    | None -> []
    | Some x -> [x]
  in
  let str_to_list r =
    List.flatten [
      option_to_list r.V11.tres;
      option_to_list r.V11.zres;
      option_to_list r.V11.ires;
      option_to_list r.V11.smtres;
      option_to_list r.V11.cooperres;
      option_to_list r.V11.yres;
      option_to_list r.V11.z3res;
      option_to_list r.V11.cvc3res;
      option_to_list r.V11.smt2libres;
      option_to_list r.V11.smt2z3res;
      option_to_list r.V11.smt3res;
      option_to_list r.V11.z33res;
      option_to_list r.V11.cvc33res;
      option_to_list r.V11.yices3res;
      option_to_list r.V11.veritres;
      option_to_list r.V11.spassres;
      option_to_list r.V11.tptpres;
    ]
  in
  add_v11l (tr_fp fp) (str_to_list str)
;;

let add_v12l fp stil =
  let tr_fp x = x in
  let tr_floatomega x =
    match x with
    | V12.F f -> F f
    | V12.Omega -> F infinity
  in
  let rec tr_method m =
    match m with
    | V12.(Isabelle {isabelle_timeout = tmo; isabelle_tactic = tac}) ->
      Isabelle {isabelle_timeout = tr_floatomega tmo; isabelle_tactic = tac}
    | V12.(Zenon {zenon_timeout = t; zenon_fallback = mm}) ->
      Zenon {zenon_timeout = t; zenon_fallback = tr_method mm}
    | V12.Smt -> SmtT (F infinity)
    | V12.SmtT tmo -> SmtT (tr_floatomega tmo)
    | V12.Yices -> YicesT (F infinity)
    | V12.YicesT tmo -> YicesT (tr_floatomega tmo)
    | V12.Z3 -> Z3T (F infinity)
    | V12.Z3T tmo -> Z3T (tr_floatomega tmo)
    | V12.Cooper -> Cooper
    | V12.Sorry -> Sorry
    | V12.Fail -> Fail
    | V12.Cvc3T tmo -> Cvc3T (tr_floatomega tmo)
    | V12.Smt2lib tmo -> Smt2lib (tr_floatomega tmo)
    | V12.Smt2z3 tmo -> Smt2z3 (tr_floatomega tmo)
    | V12.Smt3 tmo -> Smt2z3 (tr_floatomega tmo)
    | V12.Z33 tmo -> Z33 (tr_floatomega tmo)
    | V12.Cvc33 tmo -> Cvc33 (tr_floatomega tmo)
    | V12.Yices3 tmo -> Yices3 (tr_floatomega tmo)
    | V12.Verit tmo -> Verit (tr_floatomega tmo)
    | V12.Spass tmo -> Spass (tr_floatomega tmo)
    | V12.Tptp tmo -> Tptp (tr_floatomega tmo)
    | V12.LS4 tmo -> LS4 (tr_floatomega tmo)
  in
  let tr_reason_option x =
    match x with
    | None -> None
    | Some V12.False -> Some False
    | Some V12.Timeout -> Some Timeout
    | Some (V12.Cantwork s) -> Some (Cantwork s)
  in
  let tr_st st =
    match st with
    | V12.Triv -> Triv
    | V12.NTriv (V12.RSucc, m) -> NTriv (RSucc, tr_method m)
    | V12.NTriv (V12.RFail r, m) ->
      NTriv (RFail (tr_reason_option r), tr_method m)
    | V12.NTriv (V12.RInt, m) -> NTriv (RInt, tr_method m)
  in
  let tr_sti (st, dt, pmv, zv, iv) =
    try [(tr_st st, dt, pmv, zv, iv)]
    with Failure _ -> []
  in
  add_to_table (tr_fp fp) (List.flatten (List.map tr_sti stil))
;;

let add_v12r fp str =
  let tr_fp x = x in
  let option_to_list x =
    match x with
    | None -> []
    | Some x -> [x]
  in
  let str_to_list r =
    List.flatten [
      option_to_list r.V12.tres;
      option_to_list r.V12.zres;
      option_to_list r.V12.ires;
      option_to_list r.V12.smtres;
      option_to_list r.V12.cooperres;
      option_to_list r.V12.yres;
      option_to_list r.V12.z3res;
      option_to_list r.V12.cvc3res;
      option_to_list r.V12.smt2libres;
      option_to_list r.V12.smt2z3res;
      option_to_list r.V12.smt3res;
      option_to_list r.V12.z33res;
      option_to_list r.V12.cvc33res;
      option_to_list r.V12.yices3res;
      option_to_list r.V12.veritres;
      option_to_list r.V12.spassres;
      option_to_list r.V12.tptpres;
    ]
  in
  add_v12l (tr_fp fp) (str_to_list str)
;;

let add_v13l fp stl = add_to_table fp stl;;

let iter_tbl vnum f fps =
  Errors.err "Translating fingerprints from version %d to version %d"
             vnum version;
  Hashtbl.iter f fps;
;;

let iter_file f ic =
  try while true do
    let v = Marshal.from_channel ic in
    f v;
  done with
  | End_of_file -> ()
  | Failure _ -> ()  (* truncated object *)
;;

let translate v ic =
  match v with
  | FP1 (zv, iv, fps) -> iter_tbl 1 (add_v1 zv iv) fps
  | FP2 fps -> iter_tbl 2 add_v2 fps;
  | FP3 fps -> iter_tbl 3 add_v3 fps;
  | FP4 fps -> iter_tbl 4 add_v4 fps;
  | FP5 fps -> iter_tbl 5 add_v5 fps; iter_file add_v5 ic;
  | FP6 fps -> iter_tbl 6 add_v6r fps; iter_file add_v6l ic;
  | FP7 fps -> iter_tbl 7 add_v7r fps; iter_file add_v7l ic;
  | FP8 fps -> iter_tbl 8 add_v8r fps; iter_file add_v8l ic;
  | FP9 fps -> iter_tbl 9 add_v9r fps; iter_file add_v9l ic;
  | FP10 fps -> iter_tbl 10 add_v10r fps; iter_file add_v10l ic;
  | FP11 fps -> iter_tbl 11 add_v11r fps; iter_file add_v11l ic;
  | FP12 fps -> iter_tbl 12 add_v12r fps; iter_file add_v12l ic;
  | FP13 fps -> fptbl := fps; iter_file add_v13l ic;
  | _ -> assert false
;;

let load_fingerprints_aux file =
  if Sys.file_exists file then begin
    let ic = open_in_bin file in
    let magic = Marshal.from_channel ic in
    if magic <> magic_number then failwith "corrupted fingerprint file";
    let v = Marshal.from_channel ic in
    if v >= FPunknown ()
      then Errors.fatal "fingerprint file is from a newer version of tlapm";
    translate v ic;
    close_in ic;
    if !Params.safefp then begin
      (* Erase fingerprints from other versions of Zenon and Isabelle. *)
      let oldtbl = !fptbl in
      fptbl := Hashtbl.create 500;
      let zv0 = Params.get_zenon_verfp () in
      let iv0 = Params.get_isabelle_version () in
      let keep (st, _, _, zv, iv) =
        match st with
        | NTriv (_, Zenon _) -> zv = zv0
        | NTriv (_, Isabelle _) -> iv = iv0
        | _ -> true
      in
      let process fp r =
        let l = List.filter keep (record_to_list r) in
        Hashtbl.add !fptbl fp (list_to_record l);
      in
      Hashtbl.iter process oldtbl;
    end;
  end;
;;

let previous_fp_file file =
  let histdir = file ^ ".history" in
  let cmd = sprintf "ls -td %s/*/*.fp" (FN.quote histdir) in
  let ic = Unix.open_process_in cmd in
  let prev = input_line ic in
  close_in ic;
  prev
;;

let load_fingerprints file =
  try
    load_fingerprints_aux file
  with e1 ->
    try
      Sys.rename file (file ^ ".corrupted");
      let prev = previous_fp_file file in
      load_fingerprints_aux prev;
      Errors.err "Cannot load fingerprints file: %s\n\
                  previous file (%s) loaded\n" (Printexc.to_string e1) prev;
   with e2 ->
     Errors.err "Cannot load fingerprints file: %s\n\
                 Cannot load older file: %s\n" (Printexc.to_string e1)
                (Printexc.to_string e2);
;;

let print_fp_line_1 fp stl =
  let rec print_meth m =
    match m with
    | V1.Isabelle s -> printf "Isabelle (%s)" s;
    | V1.Zenon {V1.zenon_timeout = t; V1.zenon_fallback = m2} ->
       printf "Zenon{timeout = %g; fallback = " t;
       print_meth m2;
       printf "}";
    | V1.Smt -> printf "Smt";
    | V1.Cooper -> printf "Cooper";
    | V1.Sorry -> printf "Sorry";
    | V1.Fail -> printf "Fail";
  in
  let print_stat s =
    match s with
    | V1.Trivial -> printf "Trivial";
    | V1.BeingProved -> printf "BeingProved";
    | V1.Success m ->
       printf "Success (";
       print_meth m;
       printf ")";
    | V1.RFail m ->
       printf "Fail (";
       print_meth m;
       printf ")";
    | V1.Checked -> printf "Checked";
    | V1.Interrupted m ->
       printf "Interrupted (";
       print_meth m;
       printf ")";
  in
  let f x =
    printf "  ";
    print_stat x;
    printf "\n";
  in
  printf "%s :\n" fp;
  List.iter f stl;
;;

let print_fp_line_2 fp stil =
  let rec print_meth m =
    match m with
    | V2.Isabelle s -> printf "Isabelle (%S)" s;
    | V2.Zenon {V2.zenon_timeout = t; V2.zenon_fallback = m2} ->
       printf "Zenon{timeout = %g; fallback = " t;
       print_meth m2;
       printf "}";
    | V2.Smt -> printf "Smt";
    | V2.Cooper -> printf "Cooper";
    | V2.Sorry -> printf "Sorry";
    | V2.Fail -> printf "Fail";
  in
  let print_stat s =
    match s with
    | V2.Trivial -> printf "Trivial";
    | V2.BeingProved -> printf "BeingProved";
    | V2.Success m ->
       printf "Success (";
       print_meth m;
       printf ")";
    | V2.RFail m ->
       printf "Fail (";
       print_meth m;
       printf ")";
    | V2.Checked -> printf "Checked";
    | V2.Interrupted m ->
       printf "Interrupted (";
       print_meth m;
       printf ")";
  in
  let print_date (y, m, d, hr, mn, sc) =
    printf "%04d-%02d-%02dT%02d:%02d:%02d" y (m+1) d hr mn sc
  in
  let print_sti (st, d, pv, zv, iv) =
    printf "  status = "; print_stat st; printf "\n";
    printf "    date = "; print_date d; printf "\n";
    printf "    tlapm version = %S\n" pv;
    printf "    zenon version = %S\n" zv;
    printf "    isabelle version = %S\n" iv;
  in
  printf "%s :\n" fp;
  List.iter print_sti stil;
;;

let print_fp_line_3 fp stil =
  let rec print_meth m =
    match m with
    | V3.Isabelle s -> printf "Isabelle (%S)" s;
    | V3.Zenon {V3.zenon_timeout = t; V3.zenon_fallback = m2} ->
       printf "Zenon{timeout = %g; fallback = " t;
       print_meth m2;
       printf "}";
    | V3.Smt -> printf "Smt";
    | V3.Cooper -> printf "Cooper";
    | V3.Sorry -> printf "Sorry";
    | V3.Fail -> printf "Fail";
  in
  let print_stat s =
    match s with
    | V3.Trivial -> printf "Trivial";
    | V3.BeingProved -> printf "BeingProved";
    | V3.Success m ->
       printf "Success (";
       print_meth m;
       printf ")";
    | V3.RFail m ->
       printf "Fail (";
       print_meth m;
       printf ")";
    | V3.Checked -> printf "Checked";
    | V3.Interrupted m ->
       printf "Interrupted (";
       print_meth m;
       printf ")";
  in
  let print_date (y, m, d, hr, mn, sc) =
    printf "%04d-%02d-%02dT%02d:%02d:%02d" y (m+1) d hr mn sc
  in
  let print_sti (st, d, pv, zv, iv) =
    printf "  status = "; print_stat st; printf "\n";
    printf "    date = "; print_date d; printf "\n";
    printf "    tlapm version = %S\n" pv;
    printf "    zenon version = %S\n" zv;
    printf "    isabelle version = %S\n" iv;
  in
  printf "%s :\n" fp;
  List.iter print_sti stil;
;;

let print_fp_line_4 fp stil =
  let print_floatomega x =
    match x with
    | V4.F f -> printf "%g" f;
    | V4.Omega -> printf "infinity";
  in
  let rec print_meth m =
    match m with
    | V4.Isabelle {V4.isabelle_timeout = tmo; V4.isabelle_tactic = s} ->
       printf "Isabelle {timeout = ";
       print_floatomega tmo;
       printf "; tactic = %S}" s;
    | V4.Zenon {V4.zenon_timeout = t; V4.zenon_fallback = m2} ->
       printf "Zenon{timeout = %g; fallback = " t;
       print_meth m2;
       printf "}";
    | V4.Smt -> printf "Smt";
    | V4.Cooper -> printf "Cooper";
    | V4.Sorry -> printf "Sorry";
    | V4.Fail -> printf "Fail";
  in
  let print_stat s =
    match s with
    | V4.Trivial -> printf "Trivial";
    | V4.BeingProved -> printf "BeingProved";
    | V4.Success m ->
       printf "Success (";
       print_meth m;
       printf ")";
    | V4.RFail m ->
       printf "Fail (";
       print_meth m;
       printf ")";
    | V4.Checked -> printf "Checked";
    | V4.Interrupted m ->
       printf "Interrupted (";
       print_meth m;
       printf ")";
  in
  let print_date (y, m, d, hr, mn, sc) =
    printf "%04d-%02d-%02dT%02d:%02d:%02d" y (m+1) d hr mn sc
  in
  let print_sti (st, d, pv, zv, iv) =
    printf "  status = "; print_stat st; printf "\n";
    printf "    date = "; print_date d; printf "\n";
    printf "    tlapm version = %S\n" pv;
    printf "    zenon version = %S\n" zv;
    printf "    isabelle version = %S\n" iv;
  in
  printf "%s :\n" fp;
  List.iter print_sti stil;
;;

let print_fp_line_5 fp stil =
  let print_floatomega x =
    match x with
    | V5.F f -> printf "%g" f;
    | V5.Omega -> printf "infinity";
  in
  let rec print_meth m =
    match m with
    | V5.Isabelle {V5.isabelle_timeout = tmo; V5.isabelle_tactic = s} ->
       printf "Isabelle {timeout = ";
       print_floatomega tmo;
       printf "; tactic = %S}" s;
    | V5.Zenon {V5.zenon_timeout = t; V5.zenon_fallback = m2} ->
       printf "Zenon{timeout = %g; fallback = " t;
       print_meth m2;
       printf "}";
    | V5.Smt -> printf "Smt";
    | V5.Cooper -> printf "Cooper";
    | V5.Sorry -> printf "Sorry";
    | V5.Fail -> printf "Fail";
  in
  let print_stat s =
    match s with
    | V5.Trivial -> printf "Trivial";
    | V5.BeingProved -> printf "BeingProved";
    | V5.Success m ->
       printf "Success (";
       print_meth m;
       printf ")";
    | V5.RFail m ->
       printf "Fail (";
       print_meth m;
       printf ")";
    | V5.Checked -> printf "Checked";
    | V5.Interrupted m ->
       printf "Interrupted (";
       print_meth m;
       printf ")";
  in
  let print_reason r =
    match r with
    | None -> printf "None";
    | Some V5.False -> printf "False";
    | Some V5.Timeout -> printf "Timeout";
  in
  let print_date (y, m, d, hr, mn, sc) =
    printf "%04d-%02d-%02dT%02d:%02d:%02d" y (m+1) d hr mn sc
  in
  let print_sti (st, r, d, pv, zv, iv) =
    printf "    status = "; print_stat st; printf "\n";
    printf "      reason = "; print_reason r; printf "\n";
    printf "      date = "; print_date d; printf "\n";
    printf "      tlapm version = %S\n" pv;
    printf "      zenon version = %S\n" zv;
    printf "      isabelle version = %S\n" iv;
  in
  printf "  %s :\n" fp;
  List.iter print_sti stil;
;;

let print_sti_6 (st, d, pv, zv, iv) =
  let print_floatomega x =
    match x with
    | V6.F f -> printf "%g" f;
    | V6.Omega -> printf "infinity";
  in
  let rec print_meth m =
    match m with
    | V6.Isabelle {V6.isabelle_timeout = tmo; V6.isabelle_tactic = s} ->
       printf "Isabelle {timeout = ";
       print_floatomega tmo;
       printf "; tactic = %S}" s;
    | V6.Zenon {V6.zenon_timeout = t; V6.zenon_fallback = m2} ->
       printf "Zenon{timeout = %g; fallback = " t;
       print_meth m2;
       printf "}";
    | V6.Smt -> printf "Smt";
    | V6.Unusable1 -> printf "Ambiguous method (Cooper or Yices)";
    | V6.Unusable2 -> printf "Ambiguous method (Sorry or Cooper)";
    | V6.Unusable3 -> printf "Ambiguous method (Fail or Sorry)";
    | V6.Fail -> printf "Fail";
  in
  let print_reason r =
    match r with
    | None -> printf "No reason";
    | Some V6.False -> printf "False";
    | Some V6.Timeout -> printf "Timeout";
  in
  let print_stat s =
    match s with
    | V6.Triv -> printf "Trivial";
    | V6.NTriv (V6.RSucc, m) ->
       printf "RSucc (";
       print_meth m;
       printf ")";
    | V6.NTriv (V6.RFail r, m) ->
       printf "Fail (";
       print_reason r;
       printf ", ";
       print_meth m;
       printf ")";
    | V6.NTriv (V6.RInt, m) ->
       printf "RInt (";
       print_meth m;
       printf ")";
  in
  let print_date (y, m, d, hr, mn, sc) =
    printf "%04d-%02d-%02dT%02d:%02d:%02d" y (m+1) d hr mn sc
  in
  printf "    status = "; print_stat st; printf "\n";
  printf "      date = "; print_date d; printf "\n";
  printf "      tlapm version = %S\n" pv;
  printf "      zenon version = %S\n" zv;
  printf "      isabelle version = %S\n" iv;
;;

let print_fp_line_6r fp str =
  let print_sti_opt lbl o =
    match o with
    | None -> ()
    | Some sti ->
       printf "    %s:\n" lbl;
       print_sti_6 sti;
  in
  printf "  %s :\n" fp;
  print_sti_opt "Trivial" str.V6.tres;
  print_sti_opt "Zenon" str.V6.zres;
  print_sti_opt "Isabelle" str.V6.ires;
  print_sti_opt "SMT" str.V6.smtres;
  print_sti_opt "Cooper" str.V6.cooperres;
;;

let print_fp_line_6l fp stil =
  printf "  %s :\n" fp;
  List.iter print_sti_6 stil;
;;

let print_sti_7 (st, d, pv, zv, iv) =
  let print_floatomega x =
    match x with
    | V7.F f -> printf "%g" f;
    | V7.Omega -> printf "infinity";
  in
  let rec print_meth m =
    match m with
    | V7.Isabelle {V7.isabelle_timeout = tmo; V7.isabelle_tactic = s} ->
       printf "Isabelle {timeout = ";
       print_floatomega tmo;
       printf "; tactic = %S}" s;
    | V7.Zenon {V7.zenon_timeout = t; V7.zenon_fallback = m2} ->
       printf "Zenon{timeout = %g; fallback = " t;
       print_meth m2;
       printf "}";
    | V7.Smt -> printf "Smt";
    | V7.Yices -> printf "Yices";
    | V7.Cooper -> printf "Cooper";
    | V7.Sorry -> printf "Sorry";
    | V7.Fail -> printf "Fail";
  in
  let print_reason r =
    match r with
    | None -> printf "No reason";
    | Some V7.False -> printf "False";
    | Some V7.Timeout -> printf "Timeout";
    | Some V7.Cantwork s -> printf "Cantwork (%S)" s;
  in
  let print_stat s =
    match s with
    | V7.Triv -> printf "Trivial";
    | V7.NTriv (V7.RSucc, m) ->
       printf "RSucc (";
       print_meth m;
       printf ")";
    | V7.NTriv (V7.RFail r, m) ->
       printf "Fail (";
       print_reason r;
       printf ", ";
       print_meth m;
       printf ")";
    | V7.NTriv (V7.RInt, m) ->
       printf "RInt (";
       print_meth m;
       printf ")";
  in
  let print_date (y, m, d, hr, mn, sc) =
    printf "%04d-%02d-%02dT%02d:%02d:%02d" y (m+1) d hr mn sc
  in
  printf "    status = "; print_stat st; printf "\n";
  printf "      date = "; print_date d; printf "\n";
  printf "      tlapm version = %S\n" pv;
  printf "      zenon version = %S\n" zv;
  printf "      isabelle version = %S\n" iv;
;;

let print_fp_line_7r fp str =
  let print_sti_opt lbl o =
    match o with
    | None -> ()
    | Some sti ->
       printf "    %s:\n" lbl;
       print_sti_7 sti;
  in
  printf "  %s :\n" fp;
  print_sti_opt "Trivial" str.V7.tres;
  print_sti_opt "Zenon" str.V7.zres;
  print_sti_opt "Isabelle" str.V7.ires;
  print_sti_opt "SMT" str.V7.smtres;
  print_sti_opt "Cooper" str.V7.cooperres;
  print_sti_opt "Yices" str.V7.yres;
;;

let print_fp_line_7l fp stil =
  printf "  %s :\n" fp;
  List.iter print_sti_7 stil;
;;

let print_sti_8 (st, d, pv, zv, iv) =
  let print_floatomega x =
    match x with
    | V8.F f -> printf "%g" f;
    | V8.Omega -> printf "infinity";
  in
  let rec print_meth m =
    match m with
    | V8.Isabelle {V8.isabelle_timeout = tmo; V8.isabelle_tactic = s} ->
       printf "Isabelle {timeout = ";
       print_floatomega tmo;
       printf "; tactic = %S}" s;
    | V8.Zenon {V8.zenon_timeout = t; V8.zenon_fallback = m2} ->
       printf "Zenon{timeout = %g; fallback = " t;
       print_meth m2;
       printf "}";
    | V8.Smt -> printf "Smt";
    | V8.SmtT tmo ->
       printf "SmtT (";
       print_floatomega tmo;
       printf ")";
    | V8.Yices -> printf "Yices";
    | V8.YicesT tmo ->
       printf "YicesT (";
       print_floatomega tmo;
       printf ")";
    | V8.Unusable1 -> printf "ambiguous method (Cooper or Z3)"
    | V8.Z3T tmo ->
       printf "Z3T (";
       print_floatomega tmo;
       printf ")";
    | V8.Unusable2 -> printf "ambiguous method (Sorry or Cooper)";
    | V8.Unusable3 -> printf "ambiguous method (Cooper or Fail)";
    | V8.Fail -> printf "Fail";
  in
  let print_reason r =
    match r with
    | None -> printf "No reason";
    | Some V8.False -> printf "False";
    | Some V8.Timeout -> printf "Timeout";
    | Some V8.Cantwork s -> printf "Cantwork (%S)" s;
  in
  let print_stat s =
    match s with
    | V8.Triv -> printf "Trivial";
    | V8.NTriv (V8.RSucc, m) ->
       printf "RSucc (";
       print_meth m;
       printf ")";
    | V8.NTriv (V8.RFail r, m) ->
       printf "Fail (";
       print_reason r;
       printf ", ";
       print_meth m;
       printf ")";
    | V8.NTriv (V8.RInt, m) ->
       printf "RInt (";
       print_meth m;
       printf ")";
  in
  let print_date (y, m, d, hr, mn, sc) =
    printf "%04d-%02d-%02dT%02d:%02d:%02d" y (m+1) d hr mn sc
  in
  printf "    status = "; print_stat st; printf "\n";
  printf "      date = "; print_date d; printf "\n";
  printf "      tlapm version = %S\n" pv;
  printf "      zenon version = %S\n" zv;
  printf "      isabelle version = %S\n" iv;
;;

let print_fp_line_8r fp str =
  let print_sti_opt lbl o =
    match o with
    | None -> ()
    | Some sti ->
       printf "    %s:\n" lbl;
       print_sti_8 sti;
  in
  printf "  %s :\n" fp;
  print_sti_opt "Trivial" str.V8.tres;
  print_sti_opt "Zenon" str.V8.zres;
  print_sti_opt "Isabelle" str.V8.ires;
  print_sti_opt "SMT" str.V8.smtres;
  print_sti_opt "Cooper" str.V8.cooperres;
  print_sti_opt "Yices" str.V8.yres;
;;

let print_fp_line_8l fp stil =
  printf "  %s :\n" fp;
  List.iter print_sti_8 stil;
;;

let print_sti_9 (st, d, pv, zv, iv) =
  let print_floatomega x =
    match x with
    | V9.F f -> printf "%g" f;
    | V9.Omega -> printf "infinity";
  in
  let rec print_meth m =
    match m with
    | V9.Isabelle {V9.isabelle_timeout = tmo; V9.isabelle_tactic = s} ->
       printf "Isabelle {timeout = ";
       print_floatomega tmo;
       printf "; tactic = %S}" s;
    | V9.Zenon {V9.zenon_timeout = t; V9.zenon_fallback = m2} ->
       printf "Zenon{timeout = %g; fallback = " t;
       print_meth m2;
       printf "}";
    | V9.Smt -> printf "Smt";
    | V9.SmtT tmo ->
       printf "SmtT (";
       print_floatomega tmo;
       printf ")";
    | V9.Yices -> printf "Yices";
    | V9.YicesT tmo ->
       printf "YicesT (";
       print_floatomega tmo;
       printf ")";
    | V9.Z3 -> printf "Z3";
    | V9.Z3T tmo ->
       printf "Z3T (";
       print_floatomega tmo;
       printf ")";
    | V9.Cooper -> printf "Cooper";
    | V9.Sorry -> printf "Sorry";
    | V9.Fail -> printf "Fail";
    | V9.Cvc3T tmo ->
       printf "Cvc3T (";
       print_floatomega tmo;
       printf ")";
  in
  let print_reason r =
    match r with
    | None -> printf "No reason";
    | Some V9.False -> printf "False";
    | Some V9.Timeout -> printf "Timeout";
    | Some V9.Cantwork s -> printf "Cantwork (%S)" s;
  in
  let print_stat s =
    match s with
    | V9.Triv -> printf "Trivial";
    | V9.NTriv (V9.RSucc, m) ->
       printf "RSucc (";
       print_meth m;
       printf ")";
    | V9.NTriv (V9.RFail r, m) ->
       printf "Fail (";
       print_reason r;
       printf ", ";
       print_meth m;
       printf ")";
    | V9.NTriv (V9.RInt, m) ->
       printf "RInt (";
       print_meth m;
       printf ")";
  in
  let print_date (y, m, d, hr, mn, sc) =
    printf "%04d-%02d-%02dT%02d:%02d:%02d" y (m+1) d hr mn sc
  in
  printf "    status = "; print_stat st; printf "\n";
  printf "      date = "; print_date d; printf "\n";
  printf "      tlapm version = %S\n" pv;
  printf "      zenon version = %S\n" zv;
  printf "      isabelle version = %S\n" iv;
;;

let print_fp_line_9r fp str =
  let print_sti_opt lbl o =
    match o with
    | None -> ()
    | Some sti ->
       printf "    %s:\n" lbl;
       print_sti_9 sti;
  in
  printf "  %s :\n" fp;
  print_sti_opt "Trivial" str.V9.tres;
  print_sti_opt "Zenon" str.V9.zres;
  print_sti_opt "Isabelle" str.V9.ires;
  print_sti_opt "SMT" str.V9.smtres;
  print_sti_opt "Cooper" str.V9.cooperres;
  print_sti_opt "Yices" str.V9.yres;
  print_sti_opt "Z3" str.V9.z3res;
  print_sti_opt "CVC3" str.V9.cvc3res;
;;

let print_fp_line_9l fp stil =
  printf "  %s :\n" fp;
  List.iter print_sti_9 stil;
;;

let print_sti_10 (st, d, pv, zv, iv) =
  let print_floatomega x =
    match x with
    | V10.F f -> printf "%g" f;
    | V10.Omega -> printf "infinity";
  in
  let rec print_meth m =
    match m with
    | V10.Isabelle {V10.isabelle_timeout = tmo; V10.isabelle_tactic = s} ->
       printf "Isabelle {timeout = ";
       print_floatomega tmo;
       printf "; tactic = %S}" s;
    | V10.Zenon {V10.zenon_timeout = t; V10.zenon_fallback = m2} ->
       printf "Zenon{timeout = %g; fallback = " t;
       print_meth m2;
       printf "}";
    | V10.Smt -> printf "Smt";
    | V10.SmtT tmo ->
       printf "SmtT (";
       print_floatomega tmo;
       printf ")";
    | V10.Yices -> printf "Yices";
    | V10.YicesT tmo ->
       printf "YicesT (";
       print_floatomega tmo;
       printf ")";
    | V10.Z3 -> printf "Z3";
    | V10.Z3T tmo ->
       printf "Z3T (";
       print_floatomega tmo;
       printf ")";
    | V10.Cooper -> printf "Cooper";
    | V10.Sorry -> printf "Sorry";
    | V10.Fail -> printf "Fail";
    | V10.Cvc3T tmo ->
       printf "Cvc3T (";
       print_floatomega tmo;
       printf ")";
    | V10.Smt2lib tmo ->
       printf "Smt2lib (";
       print_floatomega tmo;
       printf ")";
    | V10.Smt2z3 tmo ->
       printf "Smt2z3 (";
       print_floatomega tmo;
       printf ")";
  in
  let print_reason r =
    match r with
    | None -> printf "No reason";
    | Some V10.False -> printf "False";
    | Some V10.Timeout -> printf "Timeout";
    | Some V10.Cantwork s -> printf "Cantwork (%S)" s;
  in
  let print_stat s =
    match s with
    | V10.Triv -> printf "Trivial";
    | V10.NTriv (V10.RSucc, m) ->
       printf "RSucc (";
       print_meth m;
       printf ")";
    | V10.NTriv (V10.RFail r, m) ->
       printf "Fail (";
       print_reason r;
       printf ", ";
       print_meth m;
       printf ")";
    | V10.NTriv (V10.RInt, m) ->
       printf "RInt (";
       print_meth m;
       printf ")";
  in
  let print_date (y, m, d, hr, mn, sc) =
    printf "%04d-%02d-%02dT%02d:%02d:%02d" y (m+1) d hr mn sc
  in
  printf "    status = "; print_stat st; printf "\n";
  printf "      date = "; print_date d; printf "\n";
  printf "      tlapm version = %S\n" pv;
  printf "      zenon version = %S\n" zv;
  printf "      isabelle version = %S\n" iv;
;;

let print_fp_line_10r fp str =
  let print_sti_opt lbl o =
    match o with
    | None -> ()
    | Some sti ->
       printf "    %s:\n" lbl;
       print_sti_10 sti;
  in
  printf "  %s :\n" fp;
  print_sti_opt "Trivial" str.V10.tres;
  print_sti_opt "Zenon" str.V10.zres;
  print_sti_opt "Isabelle" str.V10.ires;
  print_sti_opt "SMT" str.V10.smtres;
  print_sti_opt "Cooper" str.V10.cooperres;
  print_sti_opt "Yices" str.V10.yres;
  print_sti_opt "Z3" str.V10.z3res;
  print_sti_opt "CVC3" str.V10.cvc3res;
  print_sti_opt "Smt2lib" str.V10.smt2libres;
  print_sti_opt "Smt2z3" str.V10.smt2z3res;
;;

let print_fp_line_10l fp stil =
  printf "  %s :\n" fp;
  List.iter print_sti_10 stil;
;;

let print_sti_11 (st, d, pv, zv, iv) =
  let print_floatomega x =
    match x with
    | V11.F f -> printf "%g" f;
    | V11.Omega -> printf "infinity";
  in
  let rec print_meth m =
    match m with
    | V11.Isabelle {V11.isabelle_timeout = tmo; V11.isabelle_tactic = s} ->
       printf "Isabelle {timeout = ";
       print_floatomega tmo;
       printf "; tactic = %S}" s;
    | V11.Zenon {V11.zenon_timeout = t; V11.zenon_fallback = m2} ->
       printf "Zenon{timeout = %g; fallback = " t;
       print_meth m2;
       printf "}";
    | V11.Smt -> printf "Smt";
    | V11.SmtT tmo ->
       printf "SmtT (";
       print_floatomega tmo;
       printf ")";
    | V11.Yices -> printf "Yices";
    | V11.YicesT tmo ->
       printf "YicesT (";
       print_floatomega tmo;
       printf ")";
    | V11.Z3 -> printf "Z3";
    | V11.Z3T tmo ->
       printf "Z3T (";
       print_floatomega tmo;
       printf ")";
    | V11.Cooper -> printf "Cooper";
    | V11.Sorry -> printf "Sorry";
    | V11.Fail -> printf "Fail";
    | V11.Cvc3T tmo ->
       printf "Cvc3T (";
       print_floatomega tmo;
       printf ")";
    | V11.Smt2lib tmo ->
       printf "Smt2lib (";
       print_floatomega tmo;
       printf ")";
    | V11.Smt2z3 tmo ->
       printf "Smt2z3 (";
       print_floatomega tmo;
       printf ")";
    | V11.Smt3 tmo ->
       printf "Smt3 (";
       print_floatomega tmo;
       printf ")";
    | V11.Z33 tmo ->
       printf "Z33 (";
       print_floatomega tmo;
       printf ")";
    | V11.Cvc33 tmo ->
       printf "Cvc33 (";
       print_floatomega tmo;
       printf ")";
    | V11.Yices3 tmo ->
       printf "Yices3 (";
       print_floatomega tmo;
       printf ")";
    | V11.Verit tmo ->
       printf "Verit (";
       print_floatomega tmo;
       printf ")";
    | V11.Spass tmo ->
       printf "Spass (";
       print_floatomega tmo;
       printf ")";
    | V11.Tptp tmo ->
       printf "Tptp (";
       print_floatomega tmo;
       printf ")";
  in
  let print_reason r =
    match r with
    | None -> printf "No reason";
    | Some V11.False -> printf "False";
    | Some V11.Timeout -> printf "Timeout";
    | Some V11.Cantwork s -> printf "Cantwork (%S)" s;
  in
  let print_stat s =
    match s with
    | V11.Triv -> printf "Trivial";
    | V11.NTriv (V11.RSucc, m) ->
       printf "RSucc (";
       print_meth m;
       printf ")";
    | V11.NTriv (V11.RFail r, m) ->
       printf "Fail (";
       print_reason r;
       printf ", ";
       print_meth m;
       printf ")";
    | V11.NTriv (V11.RInt, m) ->
       printf "RInt (";
       print_meth m;
       printf ")";
  in
  let print_date (y, m, d, hr, mn, sc) =
    printf "%04d-%02d-%02dT%02d:%02d:%02d" y (m+1) d hr mn sc
  in
  printf "    status = "; print_stat st; printf "\n";
  printf "      date = "; print_date d; printf "\n";
  printf "      tlapm version = %S\n" pv;
  printf "      zenon version = %S\n" zv;
  printf "      isabelle version = %S\n" iv;
;;

let print_fp_line_11r fp str =
  let print_sti_opt lbl o =
    match o with
    | None -> ()
    | Some sti ->
       printf "    %s:\n" lbl;
       print_sti_11 sti;
  in
  printf "  %s :\n" fp;
  print_sti_opt "Trivial" str.V11.tres;
  print_sti_opt "Zenon" str.V11.zres;
  print_sti_opt "Isabelle" str.V11.ires;
  print_sti_opt "SMT" str.V11.smtres;
  print_sti_opt "Cooper" str.V11.cooperres;
  print_sti_opt "Yices" str.V11.yres;
  print_sti_opt "Z3" str.V11.z3res;
  print_sti_opt "CVC3" str.V11.cvc3res;
  print_sti_opt "Smt2lib" str.V11.smt2libres;
  print_sti_opt "Smt2z3" str.V11.smt2z3res;
  print_sti_opt "Smt3" str.V11.smt3res;
  print_sti_opt "Z33" str.V11.z33res;
  print_sti_opt "Cvc33" str.V11.cvc33res;
  print_sti_opt "Yices3" str.V11.yices3res;
  print_sti_opt "Verit" str.V11.veritres;
  print_sti_opt "Spass" str.V11.spassres;
  print_sti_opt "Tptp" str.V11.tptpres;
;;

let print_fp_line_11l fp stil =
  printf "  %s :\n" fp;
  List.iter print_sti_11 stil;
;;

let print_sti_12 (st, d, pv, zv, iv) =
  let print_floatomega x =
    match x with
    | V12.F f -> printf "%g" f;
    | V12.Omega -> printf "infinity";
  in
  let rec print_meth m =
    match m with
    | V12.Isabelle {V12.isabelle_timeout = tmo; V12.isabelle_tactic = s} ->
       printf "Isabelle {timeout = ";
       print_floatomega tmo;
       printf "; tactic = %S}" s;
    | V12.Zenon {V12.zenon_timeout = t; V12.zenon_fallback = m2} ->
       printf "Zenon{timeout = %g; fallback = " t;
       print_meth m2;
       printf "}";
    | V12.Smt -> printf "Smt";
    | V12.SmtT tmo ->
       printf "SmtT (";
       print_floatomega tmo;
       printf ")";
    | V12.Yices -> printf "Yices";
    | V12.YicesT tmo ->
       printf "YicesT (";
       print_floatomega tmo;
       printf ")";
    | V12.Z3 -> printf "Z3";
    | V12.Z3T tmo ->
       printf "Z3T (";
       print_floatomega tmo;
       printf ")";
    | V12.Cooper -> printf "Cooper";
    | V12.Sorry -> printf "Sorry";
    | V12.Fail -> printf "Fail";
    | V12.Cvc3T tmo ->
       printf "Cvc3T (";
       print_floatomega tmo;
       printf ")";
    | V12.Smt2lib tmo ->
       printf "Smt2lib (";
       print_floatomega tmo;
       printf ")";
    | V12.Smt2z3 tmo ->
       printf "Smt2z3 (";
       print_floatomega tmo;
       printf ")";
    | V12.Smt3 tmo ->
       printf "Smt3 (";
       print_floatomega tmo;
       printf ")";
    | V12.Z33 tmo ->
       printf "Z33 (";
       print_floatomega tmo;
       printf ")";
    | V12.Cvc33 tmo ->
       printf "Cvc33 (";
       print_floatomega tmo;
       printf ")";
    | V12.Yices3 tmo ->
       printf "Yices3 (";
       print_floatomega tmo;
       printf ")";
    | V12.Verit tmo ->
       printf "Verit (";
       print_floatomega tmo;
       printf ")";
    | V12.Spass tmo ->
       printf "Spass (";
       print_floatomega tmo;
       printf ")";
    | V12.Tptp tmo ->
       printf "Tptp (";
       print_floatomega tmo;
       printf ")";
    | V12.LS4 tmo ->
       printf "LS4 (";
       print_floatomega tmo;
       printf ")";
  in
  let print_reason r =
    match r with
    | None -> printf "No reason";
    | Some V12.False -> printf "False";
    | Some V12.Timeout -> printf "Timeout";
    | Some V12.Cantwork s -> printf "Cantwork (%S)" s;
  in
  let print_stat s =
    match s with
    | V12.Triv -> printf "Trivial";
    | V12.NTriv (V12.RSucc, m) ->
       printf "RSucc (";
       print_meth m;
       printf ")";
    | V12.NTriv (V12.RFail r, m) ->
       printf "Fail (";
       print_reason r;
       printf ", ";
       print_meth m;
       printf ")";
    | V12.NTriv (V12.RInt, m) ->
       printf "RInt (";
       print_meth m;
       printf ")";
  in
  let print_date (y, m, d, hr, mn, sc) =
    printf "%04d-%02d-%02dT%02d:%02d:%02d" y (m+1) d hr mn sc
  in
  printf "    status = "; print_stat st; printf "\n";
  printf "      date = "; print_date d; printf "\n";
  printf "      tlapm version = %S\n" pv;
  printf "      zenon version = %S\n" zv;
  printf "      isabelle version = %S\n" iv;
;;

let print_fp_line_12r fp str =
  let print_sti_opt lbl o =
    match o with
    | None -> ()
    | Some sti ->
       printf "    %s:\n" lbl;
       print_sti_12 sti;
  in
  printf "  %s :\n" fp;
  print_sti_opt "Trivial" str.V12.tres;
  print_sti_opt "Zenon" str.V12.zres;
  print_sti_opt "Isabelle" str.V12.ires;
  print_sti_opt "SMT" str.V12.smtres;
  print_sti_opt "Cooper" str.V12.cooperres;
  print_sti_opt "Yices" str.V12.yres;
  print_sti_opt "Z3" str.V12.z3res;
  print_sti_opt "CVC3" str.V12.cvc3res;
  print_sti_opt "Smt2lib" str.V12.smt2libres;
  print_sti_opt "Smt2z3" str.V12.smt2z3res;
  print_sti_opt "Smt3" str.V12.smt3res;
  print_sti_opt "Z33" str.V12.z33res;
  print_sti_opt "Cvc33" str.V12.cvc33res;
  print_sti_opt "Yices3" str.V12.yices3res;
  print_sti_opt "Verit" str.V12.veritres;
  print_sti_opt "Spass" str.V12.spassres;
  print_sti_opt "Tptp" str.V12.tptpres;
  print_sti_opt "LS4" str.V12.ls4res;
;;

let print_fp_line_12l fp stil =
  printf "  %s :\n" fp;
  List.iter print_sti_12 stil;
;;

let print_sti_13 (st, d, pv, zv, iv) =
    let print_floatomega x =
        match x with
        | V13.F f -> printf "%g" f;
        | V13.Omega -> printf "infinity";
    in
    let rec print_meth m =
        match m with
        | V13.Isabelle {
                V13.isabelle_timeout = tmo;
                V13.isabelle_tactic = s} ->
            printf "Isabelle {timeout = ";
            print_floatomega tmo;
            printf "; tactic = %S}" s;
        | V13.Zenon {
                V13.zenon_timeout = t;
                V13.zenon_fallback = m2} ->
            printf "Zenon {timeout = %g; fallback = " t;
            print_meth m2;
            printf "}";
        | V13.Smt -> printf "Smt";
        | V13.SmtT tmo ->
            printf "SmtT (";
            print_floatomega tmo;
            printf ")";
        | V13.Yices -> printf "Yices";
        | V13.YicesT tmo ->
            printf "YicesT (";
            print_floatomega tmo;
            printf ")";
        | V13.Z3 -> printf "Z3";
        | V13.Z3T tmo ->
            printf "Z3T";
            print_floatomega tmo;
            printf ")";
        | V13.Cooper -> printf "Cooper";
        | V13.Sorry -> printf "Sorry";
        | V13.Fail -> printf "Fail";
        | V13.Cvc3T tmo ->
            printf "Cvc3T (";
            print_floatomega tmo;
            printf ")";
        | V13.Smt2lib tmo ->
            printf "Smt2lib (";
            print_floatomega tmo;
            printf ")";
        | V13.Smt2z3 tmo ->
            printf "Smt2z3 (";
            print_floatomega tmo;
            printf ")";
        | V13.Smt3 tmo ->
            printf "Smt3 (";
            print_floatomega tmo;
            printf ")";
        | V13.Z33 tmo ->
            printf "Z33 (";
            print_floatomega tmo;
            printf ")";
        | V13.Cvc33 tmo ->
            printf "Cvc33 (";
            print_floatomega tmo;
            printf ")";
        | V13.Yices3 tmo ->
            printf "Yices3 (";
            print_floatomega tmo;
            printf ")";
        | V13.Verit tmo ->
            printf "Verit (";
            print_floatomega tmo;
            printf ")";
        | V13.Spass tmo ->
            printf "Spass (";
            print_floatomega tmo;
            printf ")";
        | V13.Tptp tmo ->
            printf "Tptp (";
            print_floatomega tmo;
            printf ")";
        | V13.LS4 tmo ->
            printf "LS4 (";
            print_floatomega tmo;
            printf ")";
        | V13.ExpandENABLED ->
            printf "ExpandENABLED";
        | V13.ExpandCdot ->
            printf "ExpandCdot";
        | V13.AutoUSE ->
            printf "Auto-expand definitions";
        | V13.Lambdify ->
            printf "Lambdify definitions";
        | V13.ENABLEDaxioms ->
            printf "ENABLED axioms";
        | V13.LevelComparison ->
            printf "Level Comparison";
        | V13.Trivial ->
            printf "Trivial backend";
    in
    let print_reason r =
        match r with
        | None -> printf "No reason";
        | Some V13.False -> printf "False";
        | Some V13.Timeout -> printf "Timeout";
        | Some V13.Cantwork s -> printf "Cantwork (%S)" s;
    in
    let print_stat s =
        match s with
        | V13.Triv -> printf "Trivial";
        | V13.NTriv (V13.RSucc, m) ->
            printf "RSucc (";
            print_meth m;
            printf ")";
        | V13.NTriv (V13.RFail r, m) ->
            printf "Fail (";
            print_reason r;
            printf ", ";
            print_meth m;
            printf ")";
        | V13.NTriv (V13.RInt, m) ->
            printf "RInt (";
            print_meth m;
            printf ")";
    in
    let print_date (y, m, d, hr, mn, sc) =
        printf "%04d-%02d-%02dT%02d:%02d:%02d" y (m+1) d hr mn sc
    in
    printf "    status = "; print_stat st; printf "\n";
    printf "    date = "; print_date d; printf "\n";
    printf "    tlapm version = %S\n" pv;
    printf "    zenon version = %S\n" zv;
    printf "    isabelle version = %S\n" iv;
;;

let print_fp_line_13r fp str =
  let print_sti_opt lbl o =
    match o with
    | None -> ()
    | Some sti ->
      printf "    %s:\n" lbl;
      print_sti_13 sti;
  in
  printf "  %s :\n" fp;
  print_sti_opt "Trivial" str.V13.tres;
  print_sti_opt "Zenon" str.V13.zres;
  print_sti_opt "Isabelle" str.V13.ires;
  print_sti_opt "SMT" str.V13.smtres;
  print_sti_opt "Cooper" str.V13.cooperres;
  print_sti_opt "Yices" str.V13.yres;
  print_sti_opt "Z3" str.V13.z3res;
  print_sti_opt "CVC3" str.V13.cvc3res;
  print_sti_opt "Smt2lib" str.V13.smt2libres;
  print_sti_opt "Smt2z3" str.V13.smt2z3res;
  print_sti_opt "Smt3" str.V13.smt3res;
  print_sti_opt "Z33" str.V13.z33res;
  print_sti_opt "Cvc33" str.V13.cvc33res;
  print_sti_opt "Yices3" str.V13.yices3res;
  print_sti_opt "Verit" str.V13.veritres;
  print_sti_opt "Spass" str.V13.spassres;
  print_sti_opt "Tptp" str.V13.tptpres;
  print_sti_opt "LS4" str.V13.ls4res;
  print_sti_opt "ExpandENABLED" str.V13.expandenabledres;
  print_sti_opt "ExpandCdot" str.V13.expandcdotres;
  print_sti_opt "Lambdify" str.V13.lambdifyres;
  print_sti_opt "ENABLED axioms" str.V13.enabledaxiomsres;
  print_sti_opt "LevelComparison" str.V13.levelcomparisonres;
;;

let print_fp_line_13l fp stil =
  printf "  %s :\n" fp;
  List.iter print_sti_13 stil;
;;

let iter_file f ic =
  try while true do
    let (fp, stil) = Marshal.from_channel ic in
    f fp stil;
  done with End_of_file -> ()
;;

let print file =
  try
    let ic = open_in_bin file in
    let stop () =
      close_in ic;
      raise Exit;
    in
    let magic = Marshal.from_channel ic in
    printf "Magic number = %d\n" magic;
    if magic <> magic_number then begin
      printf "Fingerprintf file has wrong magic number. Stopping.\n";
      stop ();
    end;
    let v = Marshal.from_channel ic in
    if v >= FPunknown () then begin
      printf "Fingerprint file is from a newer version of tlapm. Stopping.\n";
      stop ();
    end;
    begin match v with
    | FP1 (zv, iv, tbl) ->
       printf "Fingerprints version = 1\n";
       printf "Isabelle version = %S\n" iv;
       printf "Zenon version = %S\n" zv;
       Hashtbl.iter print_fp_line_1 tbl;
    | FP2 tbl ->
       printf "Fingerprints version = 2\n";
       Hashtbl.iter print_fp_line_2 tbl;
    | FP3 tbl ->
       printf "Fingerprints version = 3\n";
       Hashtbl.iter print_fp_line_3 tbl;
    | FP4 tbl ->
       printf "Fingerprints version = 4\n";
       Hashtbl.iter print_fp_line_4 tbl;
    | FP5 tbl ->
       printf "Fingerprints version = 5\n";
       printf "=========== Hashtable\n";
       Hashtbl.iter print_fp_line_5 tbl;
       printf "=========== Incremental lines\n";
       iter_file print_fp_line_5 ic;
    | FP6 tbl ->
       printf "Fingerprints version = 6\n";
       printf "=========== Hashtable\n";
       Hashtbl.iter print_fp_line_6r tbl;
       printf "=========== Incremental lines\n";
       iter_file print_fp_line_6l ic;
    | FP7 tbl ->
       printf "Fingerprints version = 7\n";
       printf "=========== Hashtable\n";
       Hashtbl.iter print_fp_line_7r tbl;
       printf "=========== Incremental lines\n";
       iter_file print_fp_line_7l ic;
    | FP8 tbl ->
       printf "Fingerprints version = 8\n";
       printf "=========== Hashtable\n";
       Hashtbl.iter print_fp_line_8r tbl;
       printf "=========== Incremental lines\n";
       iter_file print_fp_line_8l ic;
    | FP9 tbl ->
       printf "Fingerprints version = 9\n";
       printf "=========== Hashtable\n";
       Hashtbl.iter print_fp_line_9r tbl;
       printf "=========== Incremental lines\n";
       iter_file print_fp_line_9l ic;
    | FP10 tbl ->
       printf "Fingerprints version = 10\n";
       printf "=========== Hashtable\n";
       Hashtbl.iter print_fp_line_10r tbl;
       printf "=========== Incremental lines\n";
       iter_file print_fp_line_10l ic;
    | FP11 tbl ->
       printf "Fingerprints version = 11\n";
       printf "=========== Hashtable\n";
       Hashtbl.iter print_fp_line_11r tbl;
       printf "=========== Incremental lines\n";
       iter_file print_fp_line_11l ic;
    | FP12 tbl ->
       printf "Fingerprints version = 12\n";
       printf "=========== Hashtable\n";
       Hashtbl.iter print_fp_line_12r tbl;
       printf "=========== Incremental lines\n";
       iter_file print_fp_line_12l ic;
    | FP13 tbl ->
       printf "Fingerprints version = 13\n";
       printf "=========== Hashtable\n";
       Hashtbl.iter print_fp_line_13r tbl;
       printf "=========== Incremental lines\n";
       iter_file print_fp_line_13l ic;
    | _ -> assert false
    end;
    stop ();
  with Exit -> ()
;;

let same_prover p sti =
  match sti with
  | (NTriv (_, m), _, _, _, _) when prover_of_method m = p -> true
  | _ -> false
;;

let erase_results file meth =
  if not (Sys.file_exists file) then Errors.fatal "%s: file not found" file;
  load_fingerprints_aux file;
  let oldtbl = !fptbl in
  fptbl := Hashtbl.create 500;
  let process fp r =
    let p = prover_of_method (meth_to_Vx meth) in
    let keep sti = not (same_prover p sti) in
    let l = List.filter keep (record_to_list r) in
    Hashtbl.add !fptbl fp (list_to_record l);
  in
  Hashtbl.iter process oldtbl;
  let oc = fp_init file [] in
  fp_close_and_consolidate file oc;
;;

let remove fp = Hashtbl.remove !fptbl (fp_to_Vx fp);;

let rec vx_to_st6 st =
  match st with
  | Triv -> Some T.Triv
  | NTriv (sta, meth) ->
     Option.map (fun m -> T.NTriv (vx_to_sta6 sta, m)) (vx_to_meth meth)

and vx_to_sta6 sta =
  match sta with
  | RSucc -> T.RSucc
  | RFail None -> T.RFail None
  | RFail (Some r) -> T.RFail (Some (vx_to_reason r))
  | RInt -> T.RInt

and vx_to_reason r =
  match r with
  | False -> T.False
  | Timeout -> T.Timeout
  | Cantwork s -> T.Cantwork s

and vx_to_meth m =
  match m with
  | Isabelle {isabelle_timeout = tmo; isabelle_tactic = tac} ->
     Some (M.Isabelle (vx_to_floatomega tmo, tac))
  | Zenon {zenon_timeout = tmo; zenon_fallback = m} -> Some (M.Zenon tmo)
  | Smt -> Some (M.SmtT infinity)
  | SmtT tmo -> Some (M.SmtT (vx_to_floatomega tmo))
  | Yices -> Some (M.YicesT infinity)
  | YicesT tmo -> Some (M.YicesT (vx_to_floatomega tmo))
  | Z3 -> Some (M.Z3T infinity)
  | Z3T tmo -> Some (M.Z3T (vx_to_floatomega tmo))
  | Cooper -> Some M.Cooper
  | Sorry -> None
  | Fail -> Some M.Fail
  | Cvc3T tmo -> Some (M.Cvc3T (vx_to_floatomega tmo))
  | Smt2lib tmo -> Some (M.Smt2lib (vx_to_floatomega tmo))
  | Smt2z3 tmo -> Some (M.Smt2z3 (vx_to_floatomega tmo))
  | Smt3 tmo -> Some (M.Smt3 (vx_to_floatomega tmo))
  | Z33 tmo -> Some (M.Z33 (vx_to_floatomega tmo))
  | Cvc33 tmo -> Some (M.Cvc33 (vx_to_floatomega tmo))
  | Yices3 tmo -> Some (M.Yices3 (vx_to_floatomega tmo))
  | Verit tmo -> Some (M.Verit (vx_to_floatomega tmo))
  | Spass tmo -> Some (M.Spass (vx_to_floatomega tmo))
  | Tptp tmo -> Some (M.Tptp (vx_to_floatomega tmo))
  | LS4 tmo -> Some (M.LS4 (vx_to_floatomega tmo))
  | ExpandENABLED -> Some M.ExpandENABLED
  | ExpandCdot -> Some M.ExpandCdot
  | AutoUSE -> Some M.AutoUSE
  | Lambdify -> Some M.Lambdify
  | ENABLEDaxioms -> Some M.ENABLEDaxioms
  | LevelComparison -> Some M.LevelComparison
  | Trivial -> Some M.Trivial

and vx_to_floatomega f =
  match f with
  | Omega -> infinity
  | F x -> x
;;

(* FIXME don't use prover_of_method, but another function that doesn't
   erase the tactic field in the Isabelle case *)

let query fp meth =
  let m = meth_to_Vx meth in
  try
    let l = record_to_list (Hashtbl.find !fptbl (fp_to_Vx fp)) in
    let f (dom, others) (st, _, _, _, _) =
      match st with
      | Triv -> (dom, others)
      | NTriv (_, m2) when prover_of_method m2 <> prover_of_method m ->
         (dom, st :: others)
      | NTriv (RSucc, m2) -> (* FIXME success dominates shorter timeout *)
         (st :: dom, others)
      | NTriv (RFail _, m2) ->
         if get_timeout m2 >= get_timeout m
         then (st :: dom, others)
         else (dom, others)
      | NTriv (RInt, _) -> (dom, others)
    in
    let (dominators, others) = List.fold_left f ([], []) l in
    match dominators with
    | [] -> (None, List.filter_map vx_to_st6 others)
    | x :: _ -> (vx_to_st6 x, List.filter_map vx_to_st6 others)
  with
  | Not_found -> (None, [])
;;

let get_length () = Hashtbl.length !fptbl;;
