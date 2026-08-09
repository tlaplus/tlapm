(*
 * Copyright (C) 2008-2019  INRIA and Microsoft Corporation
 *)

let default_zenon_timeout = 10.
let default_ls4_timeout = 10.
let default_isabelle_timeout = 30.
let default_isabelle_tactic = "auto"
let default_yices_timeout = 30.
let default_z3_timeout = 5.
let default_cvc3_timeout = 5.
let default_smt_timeout = 5.
let default_smt2_timeout = 5.
let default_zipper_timeout = 30.
let default_spass_timeout = 5.
let default_tptp_timeout = 5.

(* A Z3 `rlimit` budget of "rN" (see issue #281) grants N times this many raw
   Z3 resource units. The base is deliberately large so that a small, readable
   budget like "r5" is a meaningful amount of work. Its purpose is
   reproducibility, not timing: the resource count -- and hence the pass/fail
   outcome -- is deterministic across machines, whereas how long it takes to
   consume that budget depends on the machine and the obligation. As a rough
   rule of thumb it is comparable to a few seconds on a typical machine, but
   that correspondence is only intuition for picking N, not a guarantee. *)
let rlimit_base = 3_000_000

(* Z3 stores `rlimit` as an unsigned 32-bit integer. *)
let max_rlimit = 0xFFFF_FFFF

type t =
  | Isabelle of float * string
  | Zenon of float
  | SmtT of float
  | YicesT of float
  | Z3T of float
  | Cooper
  | Fail
  | Cvc3T of float
  | LS4 of float
  | Smt2lib of float
  | Smt2z3 of float
  | Smt3 of float * int option
  | Z33 of float * int option
  | Cvc33 of float
  | Yices3 of float
  | Verit of float
  | Zipper of float
  | Spass of float
  | Tptp of float
  | ExpandENABLED
  | ExpandCdot
  | AutoUSE
  | Lambdify
  | ENABLEDaxioms
  | LevelComparison
  | Trivial


(* The deterministic Z3 `rlimit` budget, if the method carries one (see
   issue #281). Only the Z3-based methods `Smt3` and `Z33` can have one. *)
let smt_rlimit m =
  match m with
  | Smt3 (_, r) -> r
  | Z33 (_, r) -> r
  | _ -> None


let timeout m =
  match m with
  | Zenon f -> f
  | Isabelle (f, _) -> f
  | SmtT f -> f
  | Cvc3T f -> f
  | YicesT f -> f
  | Z3T f -> f
  | LS4 f -> f
  | Smt2lib f -> f
  | Smt2z3 f -> f
  | Cooper | Fail -> infinity
  | Smt3 (f, _) -> f
  | Z33 (f, _) -> f
  | Cvc33 f -> f
  | Yices3 f -> f
  | Verit f -> f
  | Zipper f -> f
  | Spass f -> f
  | Tptp f -> f
  | ExpandENABLED -> infinity
  | ExpandCdot -> infinity
  | AutoUSE -> infinity
  | Lambdify -> infinity
  | ENABLEDaxioms -> infinity
  | LevelComparison -> infinity
  | Trivial -> infinity

let is_temporal m =
  match m with
  | LS4 _ -> true
  | _ -> false

let scale_time m s =
  match m with
  | Zenon f -> Zenon (f *. s)
  | Isabelle (f, t) -> Isabelle (f *. s, t)
  | SmtT f -> SmtT (f *. s)
  | Cvc3T f -> Cvc3T (f *. s)
  | YicesT f -> YicesT (f *. s)
  | Z3T f -> Z3T (f *. s)
  | LS4 f -> LS4 (f *. s)
  | Smt2lib f -> Smt2lib (f *. s)
  | Smt2z3 f -> Smt2z3 (f *. s)
  | Cooper -> Cooper
  | Fail -> Fail
  | Smt3 (f, r) -> Smt3 (f *. s, r)
  | Z33 (f, r) -> Z33 (f *. s, r)
  | Cvc33 f -> Cvc33 (f *. s)
  | Yices3 f -> Yices3 (f *. s)
  | Verit f -> Verit (f *. s)
  | Zipper f -> Zipper (f *. s)
  | Spass f -> Spass (f *. s)
  | Tptp f -> Tptp (f *. s)
  | ExpandENABLED -> ExpandENABLED
  | ExpandCdot -> ExpandCdot
  | AutoUSE -> AutoUSE
  | Lambdify -> Lambdify
  | ENABLEDaxioms -> ENABLEDaxioms
  | LevelComparison -> LevelComparison
  | Trivial -> Trivial


open Format

(* These are the user-visible names of the tactics, so they have to
   be nice and friendly. *)
let pp_print_tactic ff m =
  match m with
  | Isabelle (tmo, tac) -> fprintf ff "(isabelle %s %g)" tac tmo
  | Zenon f -> fprintf ff "(zenon %g s)" f
  | LS4 f -> fprintf ff "(ls4 %g s)" f
  | SmtT f -> fprintf ff "(smt_1 %g s)" f
  | Cvc3T f -> fprintf ff "(cvc3_1 %g s)" f
  | YicesT f -> fprintf ff "(yices_1 %g s)" f
  | Z3T f -> fprintf ff "(z3_1 %g s)" f
  | Smt2lib f -> fprintf ff "(smt_2 %g s)" f
  | Smt2z3 f -> fprintf ff "(z3_2 %g s)" f
  | Smt3 (f, None) -> fprintf ff "(smt %g s)" f
  | Smt3 (_, Some r) -> fprintf ff "(smt rlimit %d)" r
  | Z33 (f, None) -> fprintf ff "(z3 %g s)" f
  | Z33 (_, Some r) -> fprintf ff "(z3 rlimit %d)" r
  | Cvc33 f -> fprintf ff "(cvc4 %g s)" f
  | Yices3 f -> fprintf ff "(yices %g s)" f
  | Verit f -> fprintf ff "(verit %g s)" f
  | Zipper f -> fprintf ff "(zipper %g s)" f
  | Spass f -> fprintf ff "(spass %g s)" f
  | Tptp f -> fprintf ff "(tptp %g s)" f
  | Cooper -> fprintf ff "(cooper)"
  | Fail -> fprintf ff "(fail)"
  | ExpandENABLED -> fprintf ff "(expandenabled)"
  | ExpandCdot -> fprintf ff "(expandcdot)"
  | AutoUSE -> fprintf ff "(autouse)"
  | Lambdify -> fprintf ff "(lambdify)"
  | ENABLEDaxioms -> fprintf ff "(enabledaxioms)"
  | LevelComparison -> fprintf ff "(levelcomparison)"
  | Trivial -> fprintf ff "(trivial)"


let pp_print_method ff meth =
  fprintf ff "@[<h>(*{ by %a }*)@]" pp_print_tactic meth


let prover_meth_of_tac tac =
  match tac with
    | Isabelle (_, tac) -> (Some "isabelle", Some tac)
    | Zenon f -> (Some "zenon", None)
    | LS4 f -> (Some "ls4", None)
    | SmtT f -> (Some "smt_1", None)
    | Cvc3T f -> (Some "cvc3_1", None)
    | YicesT f -> (Some "yices_1", None)
    | Z3T f -> (Some "z3_1", None)
    | Smt2lib f -> (Some "smt2lib", None)
    | Smt2z3 f -> (Some "smt2z3", None)
    | Smt3 _ -> (Some "smt", None)
    | Z33 _ -> (Some "z3", None)
    | Cvc33 f -> (Some "cvc4", None)
    | Yices3 f -> (Some "yices", None)
    | Verit f -> (Some "verit", None)
    | Zipper f -> (Some "zipper", None)
    | Spass f -> (Some "spass", None)
    | Tptp f -> (Some "tptp", None)
    | Cooper -> (Some "cooper", None)
    | Fail -> (Some "fail", None)
    | ExpandENABLED -> (Some "expandenabled", None)
    | ExpandCdot -> (Some "expandcdot", None)
    | AutoUSE -> (Some "autouse", None)
    | Lambdify -> (Some "lambdify", None)
    | ENABLEDaxioms -> (Some "enabledaxioms", None)
    | LevelComparison -> (Some "levelcomparison", None)
    | Trivial -> (Some "trivial", None)

let prover_name_of_tac tac =
  let prover, _meth = prover_meth_of_tac tac in
  prover

type result =
  | Proved of string
  | Failed of string
  | Timedout
  | Interrupted
  | NotTried of string
