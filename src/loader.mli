(** This module is responsible for loading modules by name.
    It will search for them in the specified paths and zips/jars.
    To support the stdin or content from the LSP server it takes
    also the module contents explicitly. *)

type t

val make : string list -> t
(** Initialize the loaded with a set of paths.
    The paths can be of two kinds:
      - Paths to directories/folders. A regular path is assumed:

            `/path/to/dir/

      - Paths to zips or jars. They can be of the following format:

            `jar:file:/path/to.jar!path/in/archive/`

        Here `zip` can be specified instead of `jar`.
        The `file:` part is optional.
        Path in the archive can have the leading `/`, it will be removed.
    *)

val close : t -> t
(** Close all the zips/jars that were opened. *)

val with_dir : t -> string -> t
(** Add directory to the search path.
    Can be used to add the current or file dir temporarily. *)

val with_module : t -> string -> string -> t
(** Add a specific module explicitly.
    Can be used to add the current or file dir temporarily. *)

val load : t -> string -> string option
(** Resolve a module name to its content. *)

(** The [Loader.Global] is a wrapper around the [Loader] to make it easier
    to pass the instance in the current prover's implementation.
    In the future this global module should be removed probably. *)
module Global : sig
  val reset : unit -> unit
  (** Cleanup all the paths to avoid reusing them in the next iteration. *)

  val setup : string list -> unit
  (** Configure new instance with the specified paths. *)

  val add_module : string -> string -> unit
  (** Add a module content explicitly. *)

  val load : string -> string option
  (** Loads a module by name and returns its content, if found. *)
end
