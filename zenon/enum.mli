(*  Copyright 2009 INRIA  *)

(** Expansion of repeating text with counters. *)

(** A template is a string of the form [s1 sep s2] where [s1] and [s2]
    are identical except for occurrences of nonnegative numbers, and
    [sep] doesn't contain any digit.  [sep] may be empty and there
    may or may not be spaces between [s1] and [sep] and between [sep]
    and [s2].

    Examples:
-   [e1, e2]
-   [foo1 (foo2 (]
-   [f (f (]
-   [aaa, aaa]

    In case of ambiguity, [sep] is taken of minimal length.  For
    example:
-   [aaaa] -> ["aa" / "" / "aa"]

*)

exception Bad_template of string;;
exception Bad_number of int;;

val expand_string : int -> string -> string;;
(** Expand a template. *)

val expand_string_rev : int -> string -> string;;
(** Expand a template in reverse order. *)

val expand_text : int -> string -> string;;
(**
  [expand_text p text] expands all the templates found between [@@@] and
  [...] in [text].  If a template is followed by [\[n+]i[\]] where i
  is an integer, expand it to [p]+i terms.  If followed by [\[n-]i[\]],
  expand it to [p]-i terms.  If followed by nothing or [[n]], expand it
  to [p] terms.  If you need to write [\[n] right after a template,
  you must prefix it with [[n]].

  If a template starts and ends with a newline (LF or CRLF), and
  it doesn't work as a plain template, remove the first and last
  newlines and try again.

  If a template is ill-formed, raise [Bad_template].  If the number
  of terms is negative, raise [Bad_number].
*)
