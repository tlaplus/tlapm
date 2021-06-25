(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

(* backend/server.ml *)

val fp_init:
    string -> string list -> out_channel
(* [fp_init fp_file source_files]
   Save the previous fingerprint file [fp_file] to a new history directory.
   Save the [source_files] (a list of source file names without the
   .tla extension) to the same history directory.
   Trim the history to 10 entries.
   Open the [fp_file] for writing, write the known results to it,
   and return its out_channel for incremental updates.
 *)

val fp_writes:
    out_channel -> string ->
    Types.status_type6 list -> unit
(* [fp_writes oc fp statuses]
   Takes as argument the output channel returned by fp_init, a fingerprint,
   and a list of results.  Adds them to the fingerprint file and to the
   internal table.
*)

val fp_close_and_consolidate:
    string -> out_channel -> unit
(* [fp_close_and_consolidate file oc]
   Takes as arguments the fingerprint file name [file] and the output
   channel [oc] returned by fp_init.  Closes [oc] and writes the
   accumulated results to [file].
*)


(* tlapm_args.ml *)

val load_fingerprints: string -> unit
(* Load the fingerprints from the given file. *)

val print: string -> unit
(* Print the contents of the given fingerprint file. *)

val erase_results: string -> Method.t -> unit
(* [erase_results fpfile meth]
   Erase from the fingerprints file [fpfile] all the results of the prover
   associated with method [meth].
   Save the old fingerprints file in the history.
*)

(* backend/prep.ml *)

val remove: string -> unit
(* [remove fp]
   Remove from the table all results on fingerprint [fp].
*)

val query:
    string -> Method.t ->
    Types.status_type6 option * Types.status_type6 list
(* [query fp meth]  returns  [same, others]
   Look for previous results for [fp] with [meth].
   [same] is [Some r] if the query is dominated by a previous result [r],
   [None] otherwise.
   [others] is the stored results of all (other than the dominating)
   provers on this [fp].

   FIXME for the time being, success with a longer timeout is deemed to
   dominate a given query.  This will change when we allow more than
   one result per prover (see already_processed in prep.ml).
*)

val get_length: unit -> int
(* Return the number of entries in the fingerprint table. *)
