(* Communication to external solvers.

Copyright (C) 2011  INRIA and Microsoft Corporation
*)
module Types: sig
    type reason =
        | False
        | Timeout
        | Cantwork of string
    type status_type_aux6 =
        | RSucc
        | RFail of reason option
        | RInt
    type status_type6 =
        | Triv
        | NTriv of status_type_aux6 * Method.t
    type package = {
        final_form: Proof.T.obligation;
        log: string list;
        proof: string;
        results: status_type6 list;
        }
end


module Fingerprints: sig
    val write_fingerprint:
        Proof.T.obligation -> Proof.T.obligation
end

module Fpfile: sig
    val fp_init:
        string -> string list -> out_channel
    val fp_writes:
        out_channel -> string ->
        Types.status_type6 list -> unit
    val fp_close_and_consolidate:
        string -> out_channel -> unit
    val load_fingerprints: string -> unit
    val print: string -> unit
    val erase_results:
        string -> Method.t -> unit
    val remove: string -> unit
    val query:
        string -> Method.t ->
            Types.status_type6 option
            * Types.status_type6 list
    val get_length: unit -> int
end


module Toolbox: sig
    val toolbox_print:
        Proof.T.obligation ->
        ?temp:bool ->
        string ->
        string option ->
        string option ->
        float ->
        bool option ->
        bool ->
        Types.reason option ->
        string ->
        float option ->
            unit
    val print_ob_number: int -> unit
    val print_message: string -> unit
    val print_message_url:
        string -> string -> unit

    val normalize: bool -> Proof.T.obligation -> Proof.T.obligation
end

module Smtlib: sig
    val repls: (char * string) list
end

module Interrupted = Interrupted

module Prep : sig
    val expand_defs:
        ?what:(Expr.T.wheredef -> bool) ->
        Proof.T.obligation ->
        Proof.T.obligation
    val have_fact :
        Expr.T.hyp Deque.dq ->
        Expr.T.expr ->
        bool
end
